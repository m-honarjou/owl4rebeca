/*
 * Copyright (C) 2016 - 2020  (See AUTHORS)
 *
 * This file is part of Owl.
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package owl.command;

import static owl.thirdparty.picocli.CommandLine.ArgGroup;
import static owl.thirdparty.picocli.CommandLine.Option;

import com.google.common.base.Preconditions;
import com.google.common.base.Stopwatch;
import com.google.common.util.concurrent.UncheckedExecutionException;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Stream;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import owl.automaton.Automaton;
import owl.automaton.Views;
import owl.automaton.acceptance.EmersonLeiAcceptance;
import owl.automaton.acceptance.OmegaAcceptanceCast;
import owl.automaton.hoa.HoaReader;
import owl.automaton.hoa.HoaWriter;
import owl.bdd.FactorySupplier;
import owl.ltl.*;
// import owl.ltl.LabelledFormula;

// import owl.ltl.Literal;
// import owl.ltl.Conjunction;


import owl.ltl.parser.LtlParser;
import owl.ltl.visitors.PrintVisitor;
import owl.thirdparty.jhoafparser.consumer.HOAConsumerException;
import owl.thirdparty.jhoafparser.consumer.HOAIntermediateStoreAndManipulate;
import owl.thirdparty.jhoafparser.owl.extensions.HOAConsumerPrintFixed;
import owl.thirdparty.jhoafparser.owl.extensions.ToStateAcceptanceFixed;
import owl.thirdparty.jhoafparser.parser.generated.ParseException;

import java.io.File;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.module.kotlin.KotlinModule;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Stream;

import static owl.thirdparty.picocli.CommandLine.ArgGroup;
import static owl.thirdparty.picocli.CommandLine.Option;

// import owl.ltl.Formula;


@SuppressWarnings("PMD.ImmutableField")
final class Mixins {

  private Mixins() {}

  static final class AutomatonReader{ 

    @Option(
      names = { "-i", "--input-file" },
      description = "Input file (default: read from stdin). If '-' is specified, then the tool "
        + "reads from stdin. This option is repeatable."
    )
    private String[] automatonFile = { "-" };

    <A extends EmersonLeiAcceptance> Stream<Automaton<Integer, ? extends A>>
      source(Class<A> acceptanceClass) {

      return Stream.of(automatonFile).flatMap(file -> {
        try (var reader = "-".equals(file)
          ? new BufferedReader(new InputStreamReader(System.in))
          : Files.newBufferedReader(Path.of(file))) {

          List<Automaton<Integer, ? extends A>> automata = new ArrayList<>();

          // Warning: the 'readStream'-method reads until the reader is exhausted and thus this
          // method blocks in while reading from stdin.
          HoaReader.readStream(reader,
            FactorySupplier.defaultSupplier()::getBddSetFactory,
            null,
            automaton -> {
              Preconditions.checkArgument(
                OmegaAcceptanceCast.isInstanceOf(automaton.acceptance().getClass(),
                  acceptanceClass),
                String.format("Expected %s, but got %s.", acceptanceClass, automaton.acceptance()));
              automata.add(OmegaAcceptanceCast.cast(automaton, acceptanceClass));
            });

          return automata.stream();
        } catch (IOException e) {
          throw new UncheckedIOException(e);
        } catch (ParseException e) {
          throw new UncheckedExecutionException(e);
        }
      });
    }
  }

  static final class AutomatonWriter {

    @Option(
      names = { "-o", "--output-file" },
      description = "Output file (default: write to stdout). If '-' is specified, then the tool "
        + "writes to stdout."
    )
    private String automatonFile = null;

    @Option(
      names = {"--complete"},
      description = "Output an automaton with a complete transition relation."
    )
    boolean complete = false;

    @Option(
      names = {"--dry-run"},
      description = "Do not output resulting automaton."
    )
    private boolean dryRun = false;

    @Option(
      names = {"--state-acceptance"},
      description = "Output an automaton with a state-based acceptance condition instead of one "
        + "with a transition-based acceptance condition. For this the acceptance marks of edges "
        + "are pushed onto the successor states. However, this simple procedure might yield "
        + "suboptimal results."
    )
    private boolean stateAcceptance = false;

    @Option(
      names = {"--state-labels"},
      description = "Annotate each state of the automaton with the 'toString()' method."
    )
    private boolean stateLabels = false;

    class Sink implements AutoCloseable {

      private final BufferedWriter writer;
      private final String subcommand;
      private final List<String> subcommandArgs;

      private Sink(String subcommand, List<String> subcommandArgs) throws IOException {
        // Normalise for '-' representing output to stdout.
        if ("-".equals(automatonFile)) {
          automatonFile = null;
        }

        if (automatonFile == null) {
          writer = new BufferedWriter(new OutputStreamWriter(System.out));
        } else {
          writer = Files.newBufferedWriter(Path.of(automatonFile));
        }

        this.subcommand = subcommand;
        this.subcommandArgs = List.copyOf(subcommandArgs);
      }

      @SuppressWarnings("PMD.AvoidReassigningParameters")
      void accept(Automaton<?, ?> automaton, String automatonName)
        throws HOAConsumerException, IOException {

        if (dryRun) {
          return;
        }

        if (complete && !automaton.is(Automaton.Property.COMPLETE)) {
          automaton = Views.complete(automaton);
        }

        var printer = new HOAConsumerPrintFixed(writer);

        // Replace this by a fixed version to preserve owl header extension in case of state
        // acceptance.
        var wrappedPrinter = stateAcceptance
          ? new HOAIntermediateStoreAndManipulate(printer, new ToStateAcceptanceFixed())
          : printer;

        HoaWriter.write(
          automaton,
          wrappedPrinter,
          stateLabels,
          subcommand,
          subcommandArgs,
          automatonName);

        writer.flush();
      }

      @Override
      public void close() throws IOException {
        writer.close();
      }
    }

    Sink sink(String subcommand, List<String> subcommandArgs) throws IOException {
      return new Sink(subcommand, subcommandArgs);
    }
  }

  static final class FormulaReader {
    @Override
    public String toString() {
      return "FormulaReader{" +
              "source=" + source +
              '}';
    }

    @ArgGroup
    private Source source = null;

    private static final class Source {

      @Override
      public String toString() {
        return "Source{" +
                "formula=" + Arrays.toString(formula) +
                '}';
      }

      @Option(
        names = {"-f", "--formula"},
        description = "Use the argument of the option as the input formula. This option is "
          + "repeatable, but cannot be combined with '-i'."
      )
      String[] formula = null;

      @Option(
        names = {"-i", "--input-file"},
        description = "Input file (default: read from stdin). The file is read line-by-line and "
          + "it is assumed that each line contains a formula. Empty lines are skipped. If '-' is "
          + "specified, then the tool reads from stdin. This option is repeatable, but cannot be "
          + "combined with '-f'."
      )
      String[] formulaFile = null;

    }

    Stream<String> stringSource() throws IOException {
      // Default to stdin.
      if (source == null) {
        source = new Source();
        source.formulaFile = new String[]{ "-" };
      }

      Stream<String> stringStream;

      if (source.formulaFile == null) {
        assert source.formula != null;
        stringStream = Stream.of(source.formula);
      } else {
        List<Stream<String>> readerStreams = new ArrayList<>(source.formulaFile.length);

        for (String file : source.formulaFile) {
          BufferedReader reader = "-".equals(file)
            ? new BufferedReader(new InputStreamReader(System.in))
            : Files.newBufferedReader(Path.of(file));

          readerStreams.add(reader.lines().onClose(() -> {
            try {
              reader.close();
            } catch (IOException ex) {
              throw new UncheckedIOException(ex);
            }
          }));
        }

        // This workaround helps against getting stuck while reading from stdin.
        stringStream = readerStreams.size() == 1
          ? readerStreams.get(0)
          : readerStreams.stream().flatMap(Function.identity());
      }

      return stringStream.filter(Predicate.not(String::isBlank));
    }

    Stream<LabelledFormula> source() throws IOException {
      return stringSource().map((String line) -> {
        try {
          return LtlParser.parse(line);
          //var test = LtlParser.parse(line);
          // var testing = convertingFacade();
          // return testing;
        } catch (RecognitionException | ParseCancellationException ex) {
          throw new IllegalArgumentException(line, ex);
        }
      });
    }

    // new
    public static LabelledFormula createExampleLabelledFormula() {

     List<String> atomicPropositions = List.of("a", "b");

     Literal p0 = new Literal(0); // "p0" -> "a"

     // Gp1
     Literal p1 = new Literal(1); // "p1" represents "b"
     GOperator Gp1 = new GOperator(p1); // G(b)

     // conjunction formula (p0 & Gp1)
     Conjunction conjunction = new Conjunction(List.of(p0, Gp1));

     // FOperator formula (F(p0 & Gp1))
     FOperator fOperator = new FOperator(conjunction);

     return LabelledFormula.of(fOperator, atomicPropositions);
   }

   // /new
  }
  // changin

    public static class LTLDefinition {

    protected Expression expression;
    protected String name;

    public Expression getExpression() {
      return expression;
    }

    public void setExpression(Expression value) {
      this.expression = value;
    }

    public String getName() {
      return name;
    }

    public void setName(String value) {
      this.name = value;
    }
  }

    public static class BinaryExpression
          extends Expression
  {

    protected Expression left;
    protected Expression right;
    protected String operator;

    public Expression getLeft() {
      return left;
    }

    public void setLeft(Expression value) {
      this.left = value;
    }

    public Expression getRight() {
      return right;
    }

    public void setRight(Expression value) {
      this.right = value;
    }

    public String getOperator() {
      return operator;
    }

    public void setOperator(String value) {
      this.operator = value;
    }

  }

    public static class TermPrimary
          extends PrimaryExpression
  {

    protected Label label;
    protected ParentSuffixPrimary parentSuffixPrimary;
    protected List<Expression> indices;
    protected String name;

    public Label getLabel() {
      return label;
    }

    public void setLabel(Label value) {
      this.label = value;
    }

    public ParentSuffixPrimary getParentSuffixPrimary() {
      return parentSuffixPrimary;
    }

    public void setParentSuffixPrimary(ParentSuffixPrimary value) {
      this.parentSuffixPrimary = value;
    }

    public List<Expression> getIndices() {
      if (indices == null) {
        indices = new ArrayList<Expression>();
      }
      return this.indices;
    }

    public String getName() {
      return name;
    }

    public void setName(String value) {
      this.name = value;
    }

  }

    public static class Expression
          extends Statement
  {

    protected Type type;

    public Type getType() {
      return type;
    }

    public void setType(Type value) {
      this.type = value;
    }

  }

  public static class PrimaryExpression
          extends Expression
  {


  }

    public static class Label {

    protected String name;

    public String getName() {
      return name;
    }

    public void setName(String value) {
      this.name = value;
    }

  }


    public static class ParentSuffixPrimary {

    protected List<Expression> arguments;
    protected Integer lineNumber;
    protected Integer character;

    public List<Expression> getArguments() {
      if (arguments == null) {
        arguments = new ArrayList<Expression>();
      }
      return this.arguments;
    }

    public Integer getLineNumber() {
      return lineNumber;
    }

    public void setLineNumber(Integer value) {
      this.lineNumber = value;
    }


    public Integer getCharacter() {
      return character;
    }


    public void setCharacter(Integer value) {
      this.character = value;
    }

  }


    public static class Type {

//    protected AbstractTypeSystem typeSystem;
    protected Integer lineNumber;
    protected Integer character;

//    public AbstractTypeSystem getTypeSystem() {
//      return typeSystem;
//    }
//
//    public void setTypeSystem(AbstractTypeSystem value) {
//      this.typeSystem = value;
//    }

    public Integer getLineNumber() {
      return lineNumber;
    }

    public void setLineNumber(Integer value) {
      this.lineNumber = value;
    }

    public Integer getCharacter() {
      return character;
    }

    public void setCharacter(Integer value) {
      this.character = value;
    }

    public String getTypeName() {
      return "General-Type";
    }

    public boolean canTypeCastTo(Type target) {
      return this.canTypeUpCastTo(target) || canTypeDownCastTo(target);
    }

    public boolean canTypeDownCastTo(Type target) {
      return target.canTypeUpCastTo(this);
    }

    public boolean canTypeUpCastTo(Type target) {
      return false;
    }

    public static Comparator<Type> getCastableComparator() {
      return new Comparator<Type>() {
        public int compare(Type base, Type target) {
          if (!base.canTypeUpCastTo(target))
            return 1;
          return 0;
        }
      };
    }

    public static Comparator<Type> getExactComparator() {
      return new Comparator<Type>() {
        public int compare(Type base, Type target) {
          if (base instanceof OrdinaryPrimitiveType) {
            if (base != target)
              return 1;
          } else if (base instanceof ArrayType) {
            if (!base.canTypeUpCastTo(target))
              return 1;
            ArrayType baseArrayType = (ArrayType) base;
            ArrayType targetArrayType = (ArrayType) target;
            if (baseArrayType.getOrdinaryPrimitiveType() != targetArrayType
                    .getOrdinaryPrimitiveType()) {
              return 1;
            }
          }
          return 0;
        }
      };
    }

  }

  public static class OrdinaryPrimitiveType
          extends Type
  {

    protected String name;

    public String getName() {
      return name;
    }

    public void setName(String value) {
      this.name = value;
    }

    @Override
    public String getTypeName() {
      return this.getName();
    }


  }

  public static class ArrayType
          extends Type
  {

    protected List<Integer> dimensions;
    protected OrdinaryPrimitiveType ordinaryPrimitiveType;

    public List<Integer> getDimensions() {
      if (dimensions == null) {
        dimensions = new ArrayList<Integer>();
      }
      return this.dimensions;
    }

    public OrdinaryPrimitiveType getOrdinaryPrimitiveType() {
      return ordinaryPrimitiveType;
    }

    public void setOrdinaryPrimitiveType(OrdinaryPrimitiveType value) {
      this.ordinaryPrimitiveType = value;
    }

    @Override
    public String getTypeName() {
      String retValueSuffix = "";
      for (int dimention : this.getDimensions())
        retValueSuffix += "[" + (dimention == 0 ? "" : dimention) + "]";
      return this.getOrdinaryPrimitiveType().getTypeName() + retValueSuffix;
    }

//    public boolean canTypeUpCastTo(Type target) {
//      if (!(target instanceof ArrayType))
//        return false;
//      ArrayType aBase = (ArrayType) this;
//      ArrayType aTarget = (ArrayType) target;
//      if (aTarget.getDimensions().size() != aBase.getDimensions().size())
//        return false;
//      for (int cnt = 0; cnt < aTarget.getDimensions().size(); cnt++)
//        if (aTarget.getDimensions().get(cnt) != aBase.getDimensions().get(cnt))
//          return false;
//      target = aTarget.getOrdinaryPrimitiveType();
//      return this.getOrdinaryPrimitiveType().canTypeUpCastTo(aTarget.getOrdinaryPrimitiveType());
//    }

  }


    public static class Annotation {

    protected Expression value;
    protected String identifier;
    protected Integer lineNumber;
    protected Integer character;

    public Expression getValue() {
      return value;
    }

    public void setValue(Expression value) {
      this.value = value;
    }

    public String getIdentifier() {
      return identifier;
    }

    public void setIdentifier(String value) {
      this.identifier = value;
    }

    public Integer getLineNumber() {
      return lineNumber;
    }

    public void setLineNumber(Integer value) {
      this.lineNumber = value;
    }

    public Integer getCharacter() {
      return character;
    }

    public void setCharacter(Integer value) {
      this.character = value;
    }

  }


    public static class Statement {

    protected Integer lineNumber;
    protected Integer character;
    protected List<Annotation> annotations;

    public List<Annotation> getAnnotations() {
      if (annotations == null) {
        annotations = new ArrayList<Annotation>();
      }
      return this.annotations;
    }

    public Integer getLineNumber() {
      return lineNumber;
    }

    public void setLineNumber(Integer value) {
      this.lineNumber = value;
    }

    public Integer getCharacter() {
      return character;
    }

    public void setCharacter(Integer value) {
      this.character = value;
    }

  }


// End: changin






//  class LTLDefinition {
//    public Expression expression;
//    public String name;
//  }


//  class Expression {
//    public List<Object> annotations;
//    public int lineNumber;
//    public int character;
//    public Object type;
//    public Expression left;
//    public Expression right;
//    public String operator;
//    public String label;
//    public TermPrimary parentSuffixPrimary;
//    public List<Object> indices;
//    public String name;
//  }


//  class TermPrimary {
//    public List<Argument> arguments;
//    public int lineNumber;
//    public int character;
//    public Object type;
//    public String label;
//    public Object parentSuffixPrimary;
//    public List<Object> indices;
//    public String name;
//  }

//  class Argument {
//    public List<Object> annotations;
//    public int lineNumber;
//    public int character;
//    public Object type;
//    public String label;
//    public Object parentSuffixPrimary;
//    public List<Object> indices;
//    public String name;
//  }






  public static class Converter {

    // public static Formula convertToFormula(BinaryExpression binaryExpression) {
    //   if ("&&".equals(binaryExpression.getOperator())) {
    //     // Handle conjunction (&&)
    //     Formula leftFormula = convertToFormula(binaryExpression.getLeft());
    //     Formula rightFormula = convertToFormula(binaryExpression.getRight());
    //     return new Conjunction(Arrays.asList(leftFormula, rightFormula));
    //   } else if ("||".equals(binaryExpression.getOperator())) {
    //     // Handle disjunction (||)
    //     Formula leftFormula = convertToFormula(binaryExpression.getLeft());
    //     Formula rightFormula = convertToFormula(binaryExpression.getRight());
    //     return new Disjunction(Arrays.asList(leftFormula, rightFormula));
    //   }else if ("G".equals(binaryExpression.getOperator())) {
    //     // Handle G operator
    //     return new GOperator(convertToFormula(binaryExpression.getLeft()));
    //   } else if ("F".equals(binaryExpression.getOperator())) {
    //     // Handle F operator
    //     return new FOperator(convertToFormula(binaryExpression.getLeft()));
    //   } else if ("M".equals(binaryExpression.getOperator())) {
    //     // Handle M operator
    //     return new MOperator(convertToFormula(binaryExpression.getLeft()), convertToFormula(binaryExpression.getRight()));
    //   }else if ("R".equals(binaryExpression.getOperator())) {
    //     // Handle R operator
    //     return new ROperator(convertToFormula(binaryExpression.getLeft()), convertToFormula(binaryExpression.getRight()));
    //   }else if ("U".equals(binaryExpression.getOperator())) {
    //     // Handle U operator
    //     return new UOperator(convertToFormula(binaryExpression.getLeft()), convertToFormula(binaryExpression.getRight()));
    //   }else if ("W".equals(binaryExpression.getOperator())) {
    //     // Handle W operator
    //     return new WOperator(convertToFormula(binaryExpression.getLeft()), convertToFormula(binaryExpression.getRight()));
    //   }else if ("X".equals(binaryExpression.getOperator())) {
    //     // Handle X operator
    //     return new XOperator(convertToFormula(binaryExpression.getLeft()));
    //   } else if ("X".equals(binaryExpression.getOperator())) {
    //     // Handle X operator
    //     return new XOperator(convertToFormula(binaryExpression.getLeft()));
    //   }
    //   return null; // Add more cases as needed
    // }

    // // Method to convert a general Expression to Formula
    // public static Formula convertToFormula(Expression expression) {
    //   if (expression instanceof TermPrimary) {
    //     TermPrimary termPrimary = (TermPrimary) expression;
    //     return new Literal(termPrimary.getCharacter());
    //   } else if (expression instanceof BinaryExpression) {
    //     return convertToFormula((BinaryExpression) expression);
    //   }
    //   return null; // Add more cases as needed
    // }

    // // Convert an LTLDefinition to LabelledFormula
    // public static LabelledFormula convertToLabelledFormula(LTLDefinition ltlDefinition) {
    //   Formula formula = convertToFormula(ltlDefinition.getExpression());
    //   BitSet atomicPropsBitSet = formula.atomicPropositions(true); // Collect atomic propositions
    //   List<String> atomicProps = LabelledFormula.bitSetToStrings(atomicPropsBitSet); // Convert BitSet to List<String>

    //   // Return LabelledFormula using the 'of' method
    //   return LabelledFormula.of(formula, atomicProps);
    // }

  }

  //    // Function to parse LTLDefinition into a LabelledFormula
  //  public static LabelledFormula parseLtlDefinitionToLabelledFormula(LTLDefinition ltlDefinition) {
  //    Formula formula = parseExpression(ltlDefinition.expression);
  //    return new AutoValue_LabelledFormula(ltlDefinition.name, formula);
  //  }

   // Function to read and parse the LTLDefinition from JSON and return a stream of LabelledFormulas
   public static Stream<LabelledFormula> parseLtlDefinitionFromJson(String filePath) throws IOException {
    //  ObjectMapper mapper = new ObjectMapper();
    //  LTLDefinition ltlDefinition;
     
     

    //  //mapper.readValue(new File(filePath), LTLDefinition.class);
    //  System.out.println(ltlDefinition);

     System.out.println("ObjectMapper function 7\n ***\n");
    return null;
    //  return Stream.of(parseLtlDefinitionToLabelledFormula(ltlDefinition));
   }
   public static void rebeca_main() {
     try {
       // Path to your JSON file
       String filePath = "ltlDefinition.json";

       // Parse the JSON and create the LabelledFormula object
       Stream<LabelledFormula> labelledFormulas = parseLtlDefinitionFromJson(filePath);

       // Print the LabelledFormula object(s)
      //  labelledFormulas.forEach(System.out::println);

     } catch (IOException e) {
       e.printStackTrace();
     }
    }















  static final class FormulaWriter {

    @Option(
      names = { "-o", "--output-file" },
      description = "Output file (default: write to stdout). If '-' is specified, then the tool "
        + "writes to stdout."
    )
    private String formulaFile = null;

    final class Sink implements AutoCloseable {

      private final BufferedWriter writer;

      private Sink() throws IOException {
        // Normalise for '-' representing output to stdout.
        if ("-".equals(formulaFile)) {
          formulaFile = null;
        }

        if (formulaFile == null) {
          writer = new BufferedWriter(new OutputStreamWriter(System.out));
        } else {
          writer = Files.newBufferedWriter(Path.of(formulaFile));
        }
      }

      void accept(LabelledFormula labelledFormula) throws IOException {
        writer.write(PrintVisitor.toString(labelledFormula, true));
        writer.write(System.lineSeparator());
        writer.flush();
      }

      @Override
      public void close() throws IOException {
        writer.close();
      }
    }

    FormulaWriter.Sink sink() throws IOException {
      return new FormulaWriter.Sink();
    }
  }

  static final class AcceptanceSimplifier {

    @Option(
      names = {"--skip-acceptance-simplifier"},
      description = "Bypass the automatic simplification of automata acceptance conditions."
    )
    boolean skipAcceptanceSimplifier = false;

  }

  static final class FormulaSimplifier {

    @Option(
      names = {"--skip-formula-simplifier"},
      description = "Bypass the automatic simplification of formulas."
    )
    boolean skipSimplifier = false;

  }

  static final class Verifier {

    @Option(
      names = "--verify",
      description = "Verify the computed result. If the verification fails the tool aborts with an "
        + "error. This flag is intended only for testing.",
      hidden = true
    )
    boolean verify = false;

  }

  @SuppressWarnings("PMD.SystemPrintln")
  static final class Diagnostics {

    private final Stopwatch stopwatch = Stopwatch.createUnstarted();

    @Option(
      names = "--diagnostics",
      description = "Print diagnostic information to stderr."
    )
    private boolean printDiagnostics = false;

    @Option(
      names = "--diagnostics-time-unit",
      description = "Select the time unit (${COMPLETION-CANDIDATES}) for reporting runtimes. The "
        + "default value is ${DEFAULT-VALUE}. Be aware that for NANOSECONDS the reporting might "
        + "not be accurate.",
      defaultValue = "MILLISECONDS"
    )
    private TimeUnit timeUnit = TimeUnit.MILLISECONDS;

    void start(String subcommand, Automaton<?, ?> automaton) {
      if (printDiagnostics) {
        System.err.printf("""
            %s:
              Input Automaton (after preprocessing):
                States: %d
                Acceptance Name: %s
                Acceptance Sets: %d
            """,
          subcommand,
          automaton.states().size(),
          automaton.acceptance().name(),
          automaton.acceptance().acceptanceSets());
        stopwatch.start();
      }
    }

    void finish(Automaton<?, ?> automaton) {
      if (printDiagnostics) {
        stopwatch.stop();
        System.err.printf("""
              Output Automaton (before postprocessing):
                States: %d
                Acceptance Name: %s
                Acceptance Sets: %d
              Runtime (without pre- and postprocessing): %d %s
            """,
          automaton.states().size(),
          automaton.acceptance().name(),
          automaton.acceptance().acceptanceSets(),
          stopwatch.elapsed(timeUnit),
          timeUnit);
      }
    }
  }
}
