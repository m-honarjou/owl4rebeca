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

import com.fasterxml.jackson.annotation.JsonSubTypes;
import com.fasterxml.jackson.annotation.JsonTypeInfo;
import com.fasterxml.jackson.core.JsonParser;
import com.fasterxml.jackson.databind.DeserializationContext;
import com.fasterxml.jackson.databind.JsonDeserializer;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.annotation.JsonDeserialize;
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

import javax.swing.plaf.synth.SynthStyle;

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


import org.rebecalang.compiler.CompilerConfig;
import org.rebecalang.compiler.modelcompiler.RebecaModelCompiler;
import org.rebecalang.compiler.modelcompiler.ScopeException;
import org.rebecalang.compiler.modelcompiler.SymbolTable;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.RebecaModel;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.*;

import org.rebecalang.compiler.utils.CodeCompilationException;
import org.rebecalang.compiler.utils.CompilerExtension;
import org.rebecalang.compiler.utils.CoreVersion;
import org.rebecalang.compiler.utils.ExceptionContainer;
import org.rebecalang.compiler.utils.Pair;
import org.springframework.beans.factory.annotation.Autowired;
// import org.springframework.test.context.ContextConfiguration;
// import org.springframework.test.context.junit.jupiter.SpringJUnitConfig;
import org.springframework.context.annotation.AnnotationConfigApplicationContext;
import org.rebecalang.compiler.propertycompiler.generalrebeca.objectmodel.AssertionDefinition;
import org.rebecalang.compiler.propertycompiler.generalrebeca.objectmodel.Definition;
import org.rebecalang.compiler.propertycompiler.generalrebeca.objectmodel.PropertyModel;
// import org.rebecalang.compiler.propertycompiler.generalrebeca.objectmodel.PropertyCompiler;

import java.util.Scanner;
import org.rebecalang.compiler.propertycompiler.*;

import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Expression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.BinaryExpression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.UnaryExpression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.DotPrimary;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.TermPrimary;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.PrimaryExpression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Literal;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.TernaryExpression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.PlusSubExpression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.CastExpression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.InstanceofExpression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.NonDetExpression;

@SuppressWarnings("PMD.ImmutableField")
public final class Mixins {

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
          // return convertingFacade();
        } catch (RecognitionException | ParseCancellationException ex) {
          throw new IllegalArgumentException(line, ex);
        }
      });
    }
  }
 




    
	private static void printExpressionDetails(org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Expression expr, String indent) {
		if (expr == null) {
			System.out.println(indent + "\"type\": \"null\"");
			return;
		}
		
		System.out.println(indent + "\"type\": \"" + expr.getClass().getSimpleName() + "\",");
		
		if (expr instanceof org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.DotPrimary) {
			org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.DotPrimary dotPrimary = (org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.DotPrimary) expr;
			System.out.println(indent + "\"left\": {");
			printExpressionDetails(dotPrimary.getLeft(), indent + "  ");
			System.out.println(indent + "},");
			System.out.println(indent + "\"right\": {");
			printExpressionDetails(dotPrimary.getRight(), indent + "  ");
			System.out.println(indent + "}");
		} else if (expr instanceof org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.UnaryExpression) {
			org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.UnaryExpression unaryExpr = (org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.UnaryExpression) expr;
			System.out.println(indent + "\"operator\": \"" + unaryExpr.getOperator() + "\",");
			System.out.println(indent + "\"expression\": {");
			printExpressionDetails(unaryExpr.getExpression(), indent + "  ");
			System.out.println(indent + "}");
		} else if (expr instanceof org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.TermPrimary) {
			org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.TermPrimary termPrimary = (org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.TermPrimary) expr;
			System.out.println(indent + "\"name\": \"" + termPrimary.getName() + "\",");
			
			// Print label details
			System.out.println(indent + "\"label\": {");
			if (termPrimary.getLabel() != null) {
				System.out.println(indent + "  \"type\": \"Label\",");
				System.out.println(indent + "  \"name\": \"" + termPrimary.getLabel().getName() + "\"");
			} else {
				System.out.println(indent + "  \"type\": \"null\"");
			}
			System.out.println(indent + "},");
			
			// Print indices
			System.out.println(indent + "\"indices\": [");
			if (termPrimary.getIndices() != null && !termPrimary.getIndices().isEmpty()) {
				for (int i = 0; i < termPrimary.getIndices().size(); i++) {
					System.out.println(indent + "  {");
					printExpressionDetails(termPrimary.getIndices().get(i), indent + "    ");
					System.out.print(indent + "  }");
					if (i < termPrimary.getIndices().size() - 1) {
						System.out.println(",");
					} else {
						System.out.println();
					}
				}
			}
			System.out.println(indent + "],");
			
			// Print type information
			System.out.println(indent + "\"typeInfo\": {");
			if (termPrimary.getType() != null) {
				System.out.println(indent + "  \"type\": \"" + termPrimary.getType().getClass().getSimpleName() + "\",");
				if (termPrimary.getType() instanceof org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.OrdinaryPrimitiveType) {
					org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.OrdinaryPrimitiveType ordType = 
						(org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.OrdinaryPrimitiveType) termPrimary.getType();
					System.out.println(indent + "  \"name\": \"" + ordType.getName() + "\"");
				} else {
					System.out.println(indent + "  \"details\": \"" + termPrimary.getType().toString() + "\"");
				}
			} else {
				System.out.println(indent + "  \"type\": \"null\"");
			}
			System.out.println(indent + "},");
			
			// Print annotations
			System.out.println(indent + "\"annotations\": [");
			if (termPrimary.getAnnotations() != null && !termPrimary.getAnnotations().isEmpty()) {
				for (int i = 0; i < termPrimary.getAnnotations().size(); i++) {
					System.out.print(indent + "  \"" + termPrimary.getAnnotations().get(i) + "\"");
					if (i < termPrimary.getAnnotations().size() - 1) {
						System.out.println(",");
					} else {
						System.out.println();
					}
				}
			}
			System.out.println(indent + "]");
		} else {
			// For other expression types, try to get common properties
			try {
				java.lang.reflect.Method[] methods = expr.getClass().getMethods();
				boolean hasProperties = false;
				for (java.lang.reflect.Method method : methods) {
					if (method.getName().startsWith("get") && method.getParameterCount() == 0 && 
						!method.getName().equals("getClass") && !method.getName().equals("getLineNumber") && 
						!method.getName().equals("getCharacter")) {
						Object value = method.invoke(expr);
						String propertyName = method.getName().substring(3).toLowerCase();
						if (value instanceof String || value instanceof Number || value instanceof Boolean) {
							if (hasProperties) System.out.println(",");
							System.out.print(indent + "\"" + propertyName + "\": \"" + value + "\"");
							hasProperties = true;
						} else if (value != null && !value.toString().contains("@")) {
							if (hasProperties) System.out.println(",");
							System.out.print(indent + "\"" + propertyName + "\": \"" + value.toString() + "\"");
							hasProperties = true;
						}
					}
				}
				if (hasProperties) System.out.println();
			} catch (Exception e) {
				System.out.println(indent + "\"details\": \"" + expr.toString() + "\"");
			}
		}
	}

  private static void printDetailedPropertyModelInformation(PropertyModel grammer){
  		// Print detailed PropertyModel information
		System.out.println("PropertyModel details:");
		System.out.println("{");
		System.out.println("  \"definitions\": [");
		if (grammer.getDefinitions() != null) {
			for (int i = 0; i < grammer.getDefinitions().size(); i++) {
				org.rebecalang.compiler.propertycompiler.generalrebeca.objectmodel.Definition def = grammer.getDefinitions().get(i);
				System.out.println("    {");
				System.out.println("      \"name\": \"" + def.getName() + "\",");
				System.out.println("      \"expression\": {");
				printExpressionDetails(def.getExpression(), "        ");
				System.out.println("      }");
				System.out.print("    }");
				if (i < grammer.getDefinitions().size() - 1) {
					System.out.println(",");
				} else {
					System.out.println();
				}
			}
		}
		System.out.println("  ],");
    System.out.println("  \"assertionDefinitions\": [");
    if (grammer.getAssertionDefinitions() != null) {
        for (int i = 0; i < grammer.getAssertionDefinitions().size(); i++) {
            AssertionDefinition assertionDef = grammer.getAssertionDefinitions().get(i);
            System.out.println("    {");
            System.out.println("      \"name\": \"" + assertionDef.getName() + "\",");
            System.out.println("      \"expression\": {");
            printExpressionDetails(assertionDef.getExpression(), "        ");
            System.out.println("      }");
            System.out.print("    }");
            if (i < grammer.getAssertionDefinitions().size() - 1) {
                System.out.println(",");
            } else {
                System.out.println();
            }
        }
    }
    System.out.println("  ]");
		System.out.println("}");
}




public static class RebecaExpressionConverter {
    
    // Map to store atomic propositions for consistent naming
    private static Map<String, Integer> atomicPropositionMap = new HashMap<>();
    private static int atomicPropositionCounter = 0;
    
    /**
     * Main conversion method for Rebeca Expression to Owl Formula
     */
    public static Formula convertToFormula(Expression expression) {
        if (expression == null) {
            return BooleanConstant.FALSE;
        }
        
        if (expression instanceof BinaryExpression) {
            return convertBinaryExpression((BinaryExpression) expression);
        } else if (expression instanceof UnaryExpression) {
            return convertUnaryExpression((UnaryExpression) expression);
        } else if (expression instanceof DotPrimary) {
            return convertDotPrimary((DotPrimary) expression);
        } else if (expression instanceof TermPrimary) {
            return convertTermPrimary((TermPrimary) expression);
        } else if (expression instanceof Literal) {
            return convertLiteral((Literal) expression);
        } else if (expression instanceof TernaryExpression) {
            return convertTernaryExpression((TernaryExpression) expression);
        } else if (expression instanceof PlusSubExpression) {
            return convertPlusSubExpression((PlusSubExpression) expression);
        } else if (expression instanceof CastExpression) {
            return convertCastExpression((CastExpression) expression);
        } else if (expression instanceof InstanceofExpression) {
            return convertInstanceofExpression((InstanceofExpression) expression);
        } else if (expression instanceof NonDetExpression) {
            return convertNonDetExpression((NonDetExpression) expression);
        }
        
        // Fallback: treat unknown expressions as atomic propositions
        System.err.println("Warning: Unknown expression type: " + expression.getClass().getSimpleName());
        return createAtomicProposition("unknown_" + expression.getClass().getSimpleName());
    }
    
    /**
     * Convert BinaryExpression to Formula
     */
    private static Formula convertBinaryExpression(BinaryExpression expr) {
        String operator = expr.getOperator();
        Formula left = convertToFormula(expr.getLeft());
        Formula right = convertToFormula(expr.getRight());
        
        switch (operator) {
            // Logical operators
            case "&&":
            case "and":
                return new Conjunction(Arrays.asList(left, right));
            case "||":
            case "or":
                return new Disjunction(Arrays.asList(left, right));
            case "->":
            case "implies":
                return new Disjunction(Arrays.asList(new Negation(left), right));
            case "<->":
            case "iff":
                return new Conjunction(Arrays.asList(
                    new Disjunction(Arrays.asList(new Negation(left), right)),
                    new Disjunction(Arrays.asList(left, new Negation(right)))
                ));
            
            // Temporal operators
            case "G":
            case "globally":
                return new GOperator(left);
            case "F":
            case "finally":
                return new FOperator(left);
            case "X":
            case "next":
                return new XOperator(left);
            case "U":
            case "until":
                return new UOperator(left, right);
            case "W":
            case "weak_until":
                return new WOperator(left, right);
            case "M":
            case "strong_release":
                return new MOperator(left, right);
            case "R":
            case "release":
                return new ROperator(left, right);
            
            // Comparison operators (treat as atomic propositions)
            case "==":
            case "!=":
            case "<":
            case "<=":
            case ">":
            case ">=":
                return createAtomicProposition(expressionToString(expr));
            
            // Arithmetic operators (treat as atomic propositions)
            case "+":
            case "-":
            case "*":
            case "/":
            case "%":
                return createAtomicProposition(expressionToString(expr));
            
            default:
                System.err.println("Warning: Unknown binary operator: " + operator);
                return createAtomicProposition(expressionToString(expr));
        }
    }
    
    /**
     * Convert UnaryExpression to Formula
     */
    private static Formula convertUnaryExpression(UnaryExpression expr) {
        String operator = expr.getOperator();
        Formula operand = convertToFormula(expr.getExpression());
        
        switch (operator) {
            case "!":
            case "not":
                return new Negation(operand);
            case "G":
            case "globally":
                return new GOperator(operand);
            case "F":
            case "finally":
                return new FOperator(operand);
            case "X":
            case "next":
                return new XOperator(operand);
            case "-":
            case "+":
                // Arithmetic unary operators - treat as atomic propositions
                return createAtomicProposition(expressionToString(expr));
            default:
                System.err.println("Warning: Unknown unary operator: " + operator);
                return createAtomicProposition(expressionToString(expr));
        }
    }
    
    /**
     * Convert DotPrimary (object.property access) to atomic proposition
     */
    private static Formula convertDotPrimary(DotPrimary expr) {
        String leftStr = expressionToString(expr.getLeft());
        String rightStr = expressionToString(expr.getRight());
        String atomicProp = leftStr + "." + rightStr;
        return createAtomicProposition(atomicProp);
    }
    
    /**
     * Convert TermPrimary to atomic proposition
     */
    private static Formula convertTermPrimary(TermPrimary expr) {
        String name = expr.getName();
        if (name != null && !name.isEmpty()) {
            return createAtomicProposition(name);
        }
        return createAtomicProposition("term_" + System.identityHashCode(expr));
    }
    
    /**
     * Convert Literal to appropriate Formula
     */
    private static Formula convertLiteral(Literal expr) {
        // Try to get the literal value
        String value = expr.getLiteralValue();
        if (value != null) {
            switch (value.toLowerCase()) {
                case "true":
                    return BooleanConstant.TRUE;
                case "false":
                    return BooleanConstant.FALSE;
                default:
                    return createAtomicProposition(value);
            }
        }
        return createAtomicProposition("literal_" + System.identityHashCode(expr));
    }
    
    /**
     * Convert TernaryExpression (condition ? true_expr : false_expr)
     */
    private static Formula convertTernaryExpression(TernaryExpression expr) {
        Formula condition = convertToFormula(expr.getCondition());
        Formula trueExpr = convertToFormula(expr.getLeft());
        Formula falseExpr = convertToFormula(expr.getRight());
        
        // (condition && trueExpr) || (!condition && falseExpr)
        return new Disjunction(Arrays.asList(
            new Conjunction(Arrays.asList(condition, trueExpr)),
            new Conjunction(Arrays.asList(new Negation(condition), falseExpr))
        ));
    }
    
    /**
     * Convert PlusSubExpression to atomic proposition
     */
    private static Formula convertPlusSubExpression(PlusSubExpression expr) {
        return createAtomicProposition(expressionToString(expr));
    }
    
    /**
     * Convert CastExpression to atomic proposition
     */
    private static Formula convertCastExpression(CastExpression expr) {
        return createAtomicProposition(expressionToString(expr));
    }
    
    /**
     * Convert InstanceofExpression to atomic proposition
     */
    private static Formula convertInstanceofExpression(InstanceofExpression expr) {
        return createAtomicProposition(expressionToString(expr));
    }
    
    /**
     * Convert NonDetExpression to atomic proposition
     */
    private static Formula convertNonDetExpression(NonDetExpression expr) {
        return createAtomicProposition(expressionToString(expr));
    }
    
    /**
     * Create an atomic proposition with consistent indexing
     */
    private static Formula createAtomicProposition(String name) {
        Integer index = atomicPropositionMap.get(name);
        if (index == null) {
            index = atomicPropositionCounter++;
            atomicPropositionMap.put(name, index);
        }
        return new owl.ltl.Literal(index);
    }
    
    /**
     * Convert expression to string representation for atomic propositions
     */
    private static String expressionToString(Expression expr) {
        if (expr instanceof TermPrimary) {
            TermPrimary term = (TermPrimary) expr;
            return term.getName() != null ? term.getName() : "term";
        } else if (expr instanceof DotPrimary) {
            DotPrimary dot = (DotPrimary) expr;
            return expressionToString(dot.getLeft()) + "." + expressionToString(dot.getRight());
        } else if (expr instanceof Literal) {
            Literal lit = (Literal) expr;
            return lit.getLiteralValue() != null ? lit.getLiteralValue() : "literal";
        } else if (expr instanceof BinaryExpression) {
            BinaryExpression bin = (BinaryExpression) expr;
            return "(" + expressionToString(bin.getLeft()) + " " + bin.getOperator() + " " + expressionToString(bin.getRight()) + ")";
        } else if (expr instanceof UnaryExpression) {
            UnaryExpression un = (UnaryExpression) expr;
            return un.getOperator() + "(" + expressionToString(un.getExpression()) + ")";
        }
        return expr.getClass().getSimpleName();
    }
    
    /**
     * Convert a Definition to LabelledFormula
     */
    public static LabelledFormula convertDefinitionToLabelledFormula(Definition definition) {
        Formula formula = convertToFormula(definition.getExpression());
        
        // Create atomic propositions list from our map
        List<String> atomicProps = new ArrayList<>();
        for (int i = 0; i < atomicPropositionCounter; i++) {
            atomicProps.add(null); // Initialize with nulls
        }
        
        // Fill in the atomic proposition names
        for (Map.Entry<String, Integer> entry : atomicPropositionMap.entrySet()) {
            atomicProps.set(entry.getValue(), entry.getKey());
        }
        
        // Remove nulls and ensure we have at least empty list
        atomicProps.removeIf(Objects::isNull);
        
        return LabelledFormula.of(formula, atomicProps);
    }
    
    /**
     * Reset the atomic proposition mapping (useful for processing multiple formulas)
     */
    public static void resetAtomicPropositions() {
        atomicPropositionMap.clear();
        atomicPropositionCounter = 0;
    }
}







    public static LabelledFormula testRebecaConverter() {
        // Create TermPrimary expressions for atomic propositions
        TermPrimary termP0s = new TermPrimary();
        termP0s.setName("p0s");

        TermPrimary termP1s = new TermPrimary();
        termP1s.setName("p1s");

        TermPrimary termP2s = new TermPrimary();
        termP2s.setName("p2s");

        // Create G(p0s) - Globally p0s
        BinaryExpression gP0s = new BinaryExpression();
        gP0s.setLeft(termP0s);
        gP0s.setOperator("G");

        // Create G(p1s) - Globally p1s
        BinaryExpression gP1s = new BinaryExpression();
        gP1s.setLeft(termP1s);
        gP1s.setOperator("G");

        // Create G(p2s) - Globally p2s
        BinaryExpression gP2s = new BinaryExpression();
        gP2s.setLeft(termP2s);
        gP2s.setOperator("G");

        // Create G(p0s) && G(p1s)
        BinaryExpression firstConjunction = new BinaryExpression();
        firstConjunction.setLeft(gP0s);
        firstConjunction.setRight(gP1s);
        firstConjunction.setOperator("&&");

        // Create (G(p0s) && G(p1s)) && G(p2s)
        BinaryExpression finalConjunction = new BinaryExpression();
        finalConjunction.setLeft(firstConjunction);
        finalConjunction.setRight(gP2s);
        finalConjunction.setOperator("&&");

        // Create Definition using the new Rebeca structure
        Definition definition = new Definition();
        definition.setExpression(finalConjunction);
        definition.setName("Safety");

        // Convert Definition to LabelledFormula using the new converter
        LabelledFormula labelledFormula = RebecaExpressionConverter.convertDefinitionToLabelledFormula(definition);

        return labelledFormula;
    }

    public static LabelledFormula testSimpleRebecaConverter() {
        // Create TermPrimary expressions
        TermPrimary termP0s = new TermPrimary();
        termP0s.setName("p0s");

        TermPrimary termP1s = new TermPrimary();
        termP1s.setName("p1s");

        // Create G(p1s)
        BinaryExpression gP1s = new BinaryExpression();
        gP1s.setLeft(termP1s);
        gP1s.setOperator("G");

        // Create p0s && G(p1s)
        BinaryExpression conjunction = new BinaryExpression();
        conjunction.setLeft(termP0s);
        conjunction.setRight(gP1s);
        conjunction.setOperator("&&");

        // Create Definition
        Definition definition = new Definition();
        definition.setExpression(conjunction);
        definition.setName("Deadlock");


        // Convert to LabelledFormula
        LabelledFormula labelledFormula = RebecaExpressionConverter.convertDefinitionToLabelledFormula(definition);

        return labelledFormula;
    }



   // Function to parse LTLDefinition into a LabelledFormula
  //  public static Stream<LabelledFormula> parseLtlDefinitionToLabelledFormula(List<LTLDefinition> ltlDefinitions) {
  //     Converter converter = new Converter();
  //     return ltlDefinitions.stream()
  //         .map(d -> converter.convertToLabelledFormula(d));
  //  }

  // public static Stream<LabelledFormula> parseDefinitionToLabelledFormula(List<Definition> ltlDefinitions) {
  //       System.out.println("parseDefinitionToLabelledFormula" + ltlDefinitions.size());

  //     NewConverter converter = new NewConverter();

  //     List<LabelledFormula> converted = new ArrayList<>();
  //     for (Definition d : ltlDefinitions) {
  //         converted.add(converter.convertDefintionToLabelledFormula(d));
  //     }
  //     return converted.stream();
  //     // return ltlDefinitions.stream()
  //     //     .map(d -> converter.convertDefintionToLabelledFormula(d));
  //  }

   // Function to read and parse the LTLDefinition from JSON and return a stream of LabelledFormulas
  //  public static List<LTLDefinition> parseLtlDefinitionFromJson(String filePath) throws IOException {
  //     ObjectMapper mapper = new ObjectMapper();

  //     Root root = mapper.readValue(new File(filePath), Root.class);
  //     return root.getDefinitions();
  //  }

  
   // Function to read and parse the LTLDefinition from JSON and return a stream of LabelledFormulas
   public static Stream<LabelledFormula> testRebecaToLTL() {
        List<LabelledFormula> labelledFormulas = new ArrayList<>();
        LabelledFormula labelledFormula1 = testRebecaConverter();
        LabelledFormula labelledFormula2 = testSimpleRebecaConverter();
        labelledFormulas.add(labelledFormula1);
        labelledFormulas.add(labelledFormula2);

        return labelledFormulas.stream();
   }

   public static Stream<LabelledFormula> rebecaToLTL(String rebeceFilePath, String propertyFilePath, Boolean print) {
    try (var ctx = new AnnotationConfigApplicationContext(CompilerConfig.class)) {
        RebecaModelCompiler modelCompiler = ctx.getBean(RebecaModelCompiler.class);
        PropertyCompiler propertyCompiler = ctx.getBean(PropertyCompiler.class);
        ExceptionContainer exceptions = ctx.getBean(ExceptionContainer.class);


        File model = new File(rebeceFilePath);
		    File property = new File(propertyFilePath);

        Set<CompilerExtension> extension = new HashSet<CompilerExtension>();
        Pair<RebecaModel, SymbolTable> modelCompilationResult = modelCompiler.compileRebecaFile(model, extension, CoreVersion.CORE_2_0);
        
        PropertyModel propertyModel = propertyCompiler.compilePropertyFile(property, modelCompilationResult.getFirst(), extension);

        if(print)
            printDetailedPropertyModelInformation(propertyModel);

        // Reset atomic propositions for fresh conversion
        RebecaExpressionConverter.resetAtomicPropositions();
        
        // Convert PropertyModel definitions directly to LabelledFormulas
        List<LabelledFormula> labelledFormulas = new ArrayList<>();
        
        if (propertyModel.getDefinitions() != null) {
            for (Definition definition : propertyModel.getDefinitions()) {
                try {
                    LabelledFormula labelledFormula = RebecaExpressionConverter.convertDefinitionToLabelledFormula(definition);
                    labelledFormulas.add(labelledFormula);
                    // System.out.println("Converted definition '" + definition.getName() + "' to formula: " + labelledFormula.formula());
                } catch (Exception e) {
                    System.err.println("Error converting definition '" + definition.getName() + "': " + e.getMessage());
                    e.printStackTrace();
                }
            }
        }

        
        return labelledFormulas.stream();
        
    } catch (Exception e) {
        System.err.println("Error in rebecaToLTL: " + e.getMessage());
        e.printStackTrace();
        return Stream.empty();
    }
    }

  // public static class LabelDeserializer extends JsonDeserializer<Label> {
  //   @Override
  //   public Label deserialize(JsonParser p, DeserializationContext ctxt) throws IOException {
  //     JsonNode node = p.getCodec().readTree(p);

  //     if (node.has("type") && "null".equals(node.get("type").asText())) {
  //       return null;
  //     }

  //     Label label = new Label();
  //     if (node.has("name")) {
  //       label.setName(node.get("name").asText());
  //     }
  //     return label;
  //   }
  // }















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
