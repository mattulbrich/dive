/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.prettyprint;


import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElements;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.Unmarshaller;
import java.io.IOException;
import java.io.InputStream;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.FunctionSymbolFamily;
import edu.kit.iti.algover.term.FunctionSymbolFamily.InstantiatedFunctionSymbol;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.FixOperatorCollection.FixOperatorInfo;

/**
 * Pretty print infix and prefix operators.
 *
 * The information about the available operators and their pretty syntax is obtained
 * from a serialized xml file.
 *
 * @see FixOperatorCollection
 * @see FixOperatorInfo
 *
 * @author mulbrich
 */
public class FixOperatorPrinterExtension implements PrettyPrintExtension {

    @Override
    public boolean canPrint(FunctionSymbol fs) {
        return FixOperatorCollection.get(fs) != null;
    }

    @Override
    public int getLeftPrecedence(ApplTerm application) {
        FixOperatorInfo info = FixOperatorCollection.get(application.getFunctionSymbol());
        return info.getPrecedence();
    }

    @Override
    public int getRightPrecedence(ApplTerm application) {
        FixOperatorInfo info = FixOperatorCollection.get(application.getFunctionSymbol());
        return info.getPrecedence();
    }

    @Override
    public void print(ApplTerm application, PrettyPrintVisitor visitor) {
        FunctionSymbol f = application.getFunctionSymbol();
        FixOperatorInfo info = FixOperatorCollection.get(f);
        if (f.getArity() == 1) {
            printPrefix(application, info, visitor);
        } else {
            assert f.getArity() == 2;
            printInfix(application, info, visitor);
        }
    }

    /*
     * Prints a term in prefix way.
     *
     * Possibly insert an extra space if needed, that is if
     * two operators follow directly one another.
     */
    private static void printPrefix(ApplTerm application, FixOperatorInfo fixOperator, PrettyPrintVisitor visitor) {

        assert application.getFunctionSymbol().getArity() == 1;

        Term subterm = application.getTerm(0);

        PrettyPrintLayouter printer = visitor.getPrinter();

        if (isOperatorChar(printer.getLastCharacter())) {
            printer.append(" ");
        }

        printer.append(fixOperator.getOp());
        printer.beginTerm(0);
        visitor.setLeftPrecedence(fixOperator.getPrecedence());
        subterm.accept(visitor, null);
        printer.endTerm();
    }

    /*
     * Prints a term in infix way.
     *
     * The first subterm is visited to be put in parens if the precedence is
     * strictly higher than that of this term.
     *
     * The second subterm is visited to be put in parens if the precedence is
     * at least as high as that of this term.
     *
     * Therefore plus(a,plus(b,c)) is put as a + (b + c)
     * and plus(plus(a,b),c) is put as a + b + c
     *
     * All operators are left associative automatically.
     *
     */
    private static void printInfix(ApplTerm application, FixOperatorInfo fixOperator, PrettyPrintVisitor visitor) {
        PrettyPrintLayouter printer = visitor.getPrinter();
        String op = fixOperator.getOp();

        printer.beginBlock(0);
        if(fixOperator.isLeftAssociative() && isChaining(fixOperator, application.getTerm(0))) {
            printer.indentBlock(0, 0);
        } else {
            printer.indentBlock(0, op.length() + 1);
        }
        printer.beginTerm(0);
        visitor.setLeftPrecedence(fixOperator.getPrecedence());
        application.getTerm(0).accept(visitor, null);
        printer.endTerm();

        printer.breakBlock(1, 0).append(op).append(" ");

        printer.beginTerm(1);
        visitor.setLeftPrecedence(fixOperator.getPrecedence() +
                (fixOperator.isLeftAssociative() ? 1 : 0));
        application.getTerm(1).accept(visitor, null);
        printer.endTerm();
        printer.endBlock();
    }

    /**
     * Find out if the given term applies the fixOperator and if that
     * is chaining,
     *
     * If true is returned, an optimised linebreak can be applied.
     *
     * @param fixOperator the operator to check for
     * @param term the term for which the test is made
     * @return true iff term uses fixOperator and that is a chaining op.
     */
    private static boolean isChaining(FixOperatorInfo fixOperator, Term term) {
        if (term instanceof ApplTerm) {
            ApplTerm applTerm = (ApplTerm) term;
            if (applTerm.getFunctionSymbol().getName().equals(fixOperator.getName())) {
                return fixOperator.isChaining();
            }
        }
        return false;
    }

    /**
     * Checks if a character is an operator char.
     */
    private static boolean isOperatorChar(char c) {
        return "+-<>&|=*/!^@.:".indexOf(c) != -1;
    }
}

@XmlRootElement(name = "operators")
class FixOperatorCollection {

    private static Map<String, FixOperatorInfo> MAP;

    @XmlElements(@XmlElement(name = "operator"))
    List<FixOperatorInfo> operators;

    public static FixOperatorInfo get(FunctionSymbol fs) {
        if (fs instanceof InstantiatedFunctionSymbol) {
            FunctionSymbolFamily family = ((InstantiatedFunctionSymbol) fs).getFamily();
            return get(family.getBaseName());
        } else {
            return get(fs.getName());
        }
    }

    public static FixOperatorInfo get(String fctname) {
        ensureMapExists();
        return MAP.get(fctname);
    }

    private static void ensureMapExists() {
        if (MAP == null) {
            try (InputStream is = FixOperatorCollection.class.getResourceAsStream("operators.xml")) {
                if (is == null) {
                    throw new IOException("unknown resource");
                }

                JAXBContext jaxbContext = JAXBContext.newInstance(FixOperatorCollection.class);

                Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
                FixOperatorCollection coll = (FixOperatorCollection) jaxbUnmarshaller.unmarshal(is);

                Map<String, FixOperatorInfo> map = new HashMap<>();
                for (FixOperatorInfo info : coll.operators) {
                    map.put(info.name, info);
                }

                MAP = map;
            } catch (Exception e) {
                e.printStackTrace();
                MAP = Collections.emptyMap();
            }

        }
    }

    static class FixOperatorInfo {

        @XmlElement
        private String name;

        @XmlElement
        private String op;

        @XmlElement
        private int precedence;

        @XmlElement
        private boolean leftAssociative = true;

        @XmlElement
        private boolean chaining = false;

        public int getPrecedence() {
            return precedence;
        }

        public boolean isLeftAssociative() {
            return leftAssociative;
        }

        public boolean isChaining() {
            return chaining;
        }

        public String getOp() {
            return op;
        }

        public String getName() {
            return name;
        }

        @Override
        public String toString() {
            return "FixOperatorInfo [name=" + name + ", op=" + op +
                    ", precedence=" + precedence + ", chaining=" + chaining + "]";
        }

    }
}

