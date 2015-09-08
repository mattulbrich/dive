package edu.kit.iti.algover.smt;

import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

import edu.kit.iti.algover.parser.PseudoParser;
import edu.kit.iti.algover.parser.PseudoTree;

public class SMTTrans {

    private static Properties OP_MAP;
    static {
        OP_MAP = new Properties();
        try(InputStream fis = SMTTrans.class.getResourceAsStream("opnames.txt")) {
            OP_MAP.load(fis);
        } catch (IOException e) {
            throw new Error(e);
        }
    }

    public CharSequence trans(PseudoTree exp) {
        switch(exp.getType()) {
        case PseudoParser.ALL:
            return transQuant("forall", exp);
        case PseudoParser.EX:
            return transQuant("exists", exp);
        case PseudoParser.LIT:
        case PseudoParser.ID:
            return exp.toString().replace('#', '$');

        case PseudoParser.AND:
        case PseudoParser.OR:
        case PseudoParser.IMPLIES:
        case PseudoParser.PLUS:
        case PseudoParser.MINUS:
        case PseudoParser.TIMES:
        case PseudoParser.UNION:
        case PseudoParser.INTERSECT:
        case PseudoParser.LT:
        case PseudoParser.LE:
        case PseudoParser.GE:
        case PseudoParser.GT:
        case PseudoParser.ARRAY_ACCESS:
        case PseudoParser.EQ:
        case PseudoParser.NOT:
            return transBinOp(exp);

        default:
            throw new Error(exp.toStringTree());
        }
    }

    private CharSequence transBinOp(PseudoTree exp) {
        String tokenText = exp.token.getText();
        String smtOP = OP_MAP.getProperty(tokenText);
        if(smtOP == null) {
            smtOP = tokenText;
        }
        StringBuilder sb = new StringBuilder();
        sb.append("(").append(smtOP).append(" ");
        for (PseudoTree child : exp.getChildren()) {
            sb.append(trans(child)).append(" ");
        }
        sb.append(")");
        return sb;
    }

    private String transQuant(String quantifier, PseudoTree exp) {
        String name = exp.getChild(0).toString().replace('#', '$');
        PseudoTree cond = exp.getChild(2);
        String type = transToType(exp.getChild(1));
        return "(" + quantifier + " ((" + name + " " + type + ")) " + trans(cond) + ")";
    }

    public String transToType(PseudoTree exp) {
        String type;
        switch(exp.getType()) {
        case PseudoParser.INT:
            type = "Int"; break;
        case PseudoParser.ARRAY:
            type = "(Array Int Int)"; break;
        case PseudoParser.SET:
            type = "(Array Int Bool)"; break;
        default: throw new Error();
        }
        return type;
    }

}
