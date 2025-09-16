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
import owl.ltl.*;
import org.rebecalang.compiler.propertycompiler.generalrebeca.objectmodel.Definition;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.*;

/**
 * Utility class for converting Rebeca expressions to OWL LTL formulas.
 * This class handles the conversion of various Rebeca expression types to their corresponding
 * LTL formula representations in the OWL library.
 */
public final class RebecaExpressionConverter {
    
    // Map to store atomic propositions for consistent naming
    private static Map<String, Integer> atomicPropositionMap = new HashMap<>();
    private static int atomicPropositionCounter = 0;

    private RebecaExpressionConverter() {
        // Utility class - prevent instantiation
    }
    
    /**
     * Main conversion method for Rebeca Expression to Owl Formula
     * 
     * @param expression the Rebeca expression to convert
     * @return the corresponding OWL Formula
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
        } else if (expression instanceof org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Literal) {
            return convertLiteral((org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Literal) expression);
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
    private static Formula convertLiteral(org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Literal expr) {
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
        } else if (expr instanceof org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Literal) {
            org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Literal lit = (org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Literal) expr;
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
     * 
     * @param definition the Rebeca Definition to convert
     * @return the corresponding LabelledFormula
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