/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.smt;

import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

/**
 * Old code. Only to be used for reference.
 *
 * @author Mattias Ulbrich
 */

@Deprecated
public class SMTTrans_Old {

    private static Properties OP_MAP;
    static {
        OP_MAP = new Properties();
        try(InputStream fis = SMTTrans_Old.class.getResourceAsStream("opnames.txt")) {
            OP_MAP.load(fis);
        } catch (IOException e) {
            throw new Error(e);
        }
    }

    public CharSequence trans(DafnyTree exp) {
        switch(exp.getType()) {
        case DafnyParser.ALL:
            return transQuant("forall", exp);
        case DafnyParser.EX:
            return transQuant("exists", exp);
        case DafnyParser.INT_LIT:
        case DafnyParser.ID:
            return exp.toString().replace('#', '$');

        case DafnyParser.AND:
        case DafnyParser.OR:
        case DafnyParser.IMPLIES:
        case DafnyParser.PLUS:
        case DafnyParser.MINUS:
        case DafnyParser.TIMES:
        case DafnyParser.UNION:
        case DafnyParser.INTERSECT:
        case DafnyParser.LT:
        case DafnyParser.LE:
        case DafnyParser.GE:
        case DafnyParser.GT:
        case DafnyParser.ARRAY_ACCESS:
        case DafnyParser.EQ:
        case DafnyParser.NOT:
            return transBinOp(exp);

        case DafnyParser.LENGTH:
            return "0";

        default:
            throw new Error(exp.toStringTree());
        }
    }

    private CharSequence transBinOp(DafnyTree exp) {
        String tokenText = exp.token.getText();
        String smtOP = OP_MAP.getProperty(tokenText);
        if(smtOP == null) {
            smtOP = tokenText;
        }
        StringBuilder sb = new StringBuilder();
        sb.append("(").append(smtOP).append(" ");
        for (DafnyTree child : exp.getChildren()) {
            sb.append(trans(child)).append(" ");
        }
        sb.append(")");
        return sb;
    }

    private String transQuant(String quantifier, DafnyTree exp) {
        String name = exp.getChild(0).toString().replace('#', '$');
        DafnyTree cond = exp.getChild(2);
        String type = transToType(exp.getChild(1));
        return "(" + quantifier + " ((" + name + " " + type + ")) " + trans(cond) + ")";
    }

    public String transToType(DafnyTree exp) {
        String type;
        switch(exp.getType()) {
        case DafnyParser.INT:
            type = "Int"; break;
        case DafnyParser.ARRAY:
            type = "(Array Int Int)"; break;
        case DafnyParser.SET:
            type = "(Array Int Bool)"; break;
        default: throw new Error();
        }
        return type;
    }

}
