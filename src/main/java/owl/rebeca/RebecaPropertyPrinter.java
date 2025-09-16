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

import org.rebecalang.compiler.propertycompiler.generalrebeca.objectmodel.AssertionDefinition;
import org.rebecalang.compiler.propertycompiler.generalrebeca.objectmodel.Definition;
import org.rebecalang.compiler.propertycompiler.generalrebeca.objectmodel.PropertyModel;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Expression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.DotPrimary;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.UnaryExpression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.TermPrimary;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.OrdinaryPrimitiveType;

/**
 * Utility class for printing detailed information about Rebeca property models and expressions.
 */
public final class RebecaPropertyPrinter {

    private RebecaPropertyPrinter() {
        // Utility class - prevent instantiation
    }

    /**
     * Prints detailed information about a PropertyModel including definitions and assertion definitions.
     * 
     * @param propertyModel the PropertyModel to print
     */
    public static void printDetailedPropertyModelInformation(PropertyModel propertyModel) {
        // Print detailed PropertyModel information
        System.out.println("PropertyModel details:");
        System.out.println("{");
        System.out.println("  \"definitions\": [");
        if (propertyModel.getDefinitions() != null) {
            for (int i = 0; i < propertyModel.getDefinitions().size(); i++) {
                Definition def = propertyModel.getDefinitions().get(i);
                System.out.println("    {");
                System.out.println("      \"name\": \"" + def.getName() + "\",");
                System.out.println("      \"expression\": {");
                printExpressionDetails(def.getExpression(), "        ");
                System.out.println("      }");
                System.out.print("    }");
                if (i < propertyModel.getDefinitions().size() - 1) {
                    System.out.println(",");
                } else {
                    System.out.println();
                }
            }
        }
        System.out.println("  ],");
        System.out.println("  \"assertionDefinitions\": [");
        if (propertyModel.getAssertionDefinitions() != null) {
            for (int i = 0; i < propertyModel.getAssertionDefinitions().size(); i++) {
                AssertionDefinition assertionDef = propertyModel.getAssertionDefinitions().get(i);
                System.out.println("    {");
                System.out.println("      \"name\": \"" + assertionDef.getName() + "\",");
                System.out.println("      \"expression\": {");
                printExpressionDetails(assertionDef.getExpression(), "        ");
                System.out.println("      }");
                System.out.print("    }");
                if (i < propertyModel.getAssertionDefinitions().size() - 1) {
                    System.out.println(",");
                } else {
                    System.out.println();
                }
            }
        }
        System.out.println("  ]");
        System.out.println("}");
    }

    /**
     * Prints detailed information about a Rebeca expression in JSON format.
     * 
     * @param expr the expression to print
     * @param indent the indentation string for formatting
     */
    public static void printExpressionDetails(Expression expr, String indent) {
        if (expr == null) {
            System.out.println(indent + "\"type\": \"null\"");
            return;
        }
        
        System.out.println(indent + "\"type\": \"" + expr.getClass().getSimpleName() + "\",");
        
        if (expr instanceof DotPrimary) {
            DotPrimary dotPrimary = (DotPrimary) expr;
            System.out.println(indent + "\"left\": {");
            printExpressionDetails(dotPrimary.getLeft(), indent + "  ");
            System.out.println(indent + "},");
            System.out.println(indent + "\"right\": {");
            printExpressionDetails(dotPrimary.getRight(), indent + "  ");
            System.out.println(indent + "}");
        } else if (expr instanceof UnaryExpression) {
            UnaryExpression unaryExpr = (UnaryExpression) expr;
            System.out.println(indent + "\"operator\": \"" + unaryExpr.getOperator() + "\",");
            System.out.println(indent + "\"expression\": {");
            printExpressionDetails(unaryExpr.getExpression(), indent + "  ");
            System.out.println(indent + "}");
        } else if (expr instanceof TermPrimary) {
            TermPrimary termPrimary = (TermPrimary) expr;
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
                if (termPrimary.getType() instanceof OrdinaryPrimitiveType) {
                    OrdinaryPrimitiveType ordType = (OrdinaryPrimitiveType) termPrimary.getType();
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
            // For other expression types, try to get common properties using reflection
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
}