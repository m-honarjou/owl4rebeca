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

package owl.rebeca;

import java.util.*;
import java.util.stream.Stream;
import owl.ltl.LabelledFormula;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.*;
import org.rebecalang.compiler.propertycompiler.generalrebeca.objectmodel.Definition;

/**
 * Utility class containing test functions for Rebeca to LTL conversion.
 * This class provides various test scenarios and examples for validating
 * the Rebeca expression conversion functionality.
 */
public final class RebecaTestUtils {

    private RebecaTestUtils() {
        // Utility class - prevent instantiation
    }

    /**
     * Test function that creates a complex LTL formula with multiple globally operators.
     * Creates the formula: G(p2s) &amp;&amp; (G(p0s) &amp;&amp; G(p1s))
     * 
     * @return LabelledFormula representing the test case
     */
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

    /**
     * Test function that creates a simple LTL formula.
     * Creates the formula: p0s &amp;&amp; G(p1s)
     * 
     * @return LabelledFormula representing the simple test case
     */
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

    /**
     * Test function that combines multiple test cases into a stream.
     * This function demonstrates how to create multiple test formulas
     * and return them as a stream for batch processing.
     * 
     * @return Stream of LabelledFormula containing test cases
     */
    public static Stream<LabelledFormula> testRebecaToLTL() {
        List<LabelledFormula> labelledFormulas = new ArrayList<>();
        LabelledFormula labelledFormula1 = testRebecaConverter();
        LabelledFormula labelledFormula2 = testSimpleRebecaConverter();
        labelledFormulas.add(labelledFormula1);
        labelledFormulas.add(labelledFormula2);

        return labelledFormulas.stream();
    }

    /**
     * Creates a test case for binary operators.
     * This method can be extended to test various binary operators
     * like &amp;&amp;, ||, -&gt;, etc.
     * 
     * @param leftProp name of the left atomic proposition
     * @param rightProp name of the right atomic proposition
     * @param operator the binary operator to test
     * @return LabelledFormula representing the binary operation test
     */
    public static LabelledFormula createBinaryOperatorTest(String leftProp, String rightProp, String operator) {
        TermPrimary leftTerm = new TermPrimary();
        leftTerm.setName(leftProp);

        TermPrimary rightTerm = new TermPrimary();
        rightTerm.setName(rightProp);

        BinaryExpression binaryExpr = new BinaryExpression();
        binaryExpr.setLeft(leftTerm);
        binaryExpr.setRight(rightTerm);
        binaryExpr.setOperator(operator);

        Definition definition = new Definition();
        definition.setExpression(binaryExpr);
        definition.setName("BinaryTest_" + operator);

        return RebecaExpressionConverter.convertDefinitionToLabelledFormula(definition);
    }

    /**
     * Creates a test case for unary operators.
     * This method can be used to test unary operators like !, G, F, X, etc.
     * 
     * @param propName name of the atomic proposition
     * @param operator the unary operator to test
     * @return LabelledFormula representing the unary operation test
     */
    public static LabelledFormula createUnaryOperatorTest(String propName, String operator) {
        TermPrimary term = new TermPrimary();
        term.setName(propName);

        UnaryExpression unaryExpr = new UnaryExpression();
        unaryExpr.setExpression(term);
        unaryExpr.setOperator(operator);

        Definition definition = new Definition();
        definition.setExpression(unaryExpr);
        definition.setName("UnaryTest_" + operator);

        return RebecaExpressionConverter.convertDefinitionToLabelledFormula(definition);
    }

    /**
     * Creates a comprehensive test suite with various operator combinations.
     * 
     * @return Stream of LabelledFormula containing comprehensive test cases
     */
    public static Stream<LabelledFormula> createComprehensiveTestSuite() {
        List<LabelledFormula> testCases = new ArrayList<>();

        // Add basic test cases
        testCases.add(testRebecaConverter());
        testCases.add(testSimpleRebecaConverter());

        // Add binary operator tests
        testCases.add(createBinaryOperatorTest("p1", "p2", "&&"));
        testCases.add(createBinaryOperatorTest("p1", "p2", "||"));
        testCases.add(createBinaryOperatorTest("p1", "p2", "->"));
        testCases.add(createBinaryOperatorTest("p1", "p2", "U"));

        // Add unary operator tests
        testCases.add(createUnaryOperatorTest("p1", "!"));
        testCases.add(createUnaryOperatorTest("p1", "G"));
        testCases.add(createUnaryOperatorTest("p1", "F"));
        testCases.add(createUnaryOperatorTest("p1", "X"));

        return testCases.stream();
    }

    
}