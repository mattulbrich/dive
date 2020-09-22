package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.VariableTerm;

import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class RecursiveSubscriptPrinterExtension implements PrettyPrintExtension, VariablePrettyPrintExtension {

    private static final String SUBSCRIPT_PATTERN = "(.*)_([0-9]+)";
    private static final int SUBSCRIPT_BASE = 0x2080;

    @Override
    public boolean canPrint(VariableTerm variable) {
        return variable.getName().matches(SUBSCRIPT_PATTERN);
    }

    @Override
    public boolean canPrint(FunctionSymbol functionSymbol) {
        return functionSymbol.getArity() == 0
                && functionSymbol.getName().matches(SUBSCRIPT_PATTERN);
    }


    @Override
    public int getLeftPrecedence(ApplTerm application) {
        return Integer.MAX_VALUE;
    }

    @Override
    public int getRightPrecedence(ApplTerm application) {
        return Integer.MAX_VALUE;
    }

    @Override
    public void print(ApplTerm application, PrettyPrintVisitor visitor) {
        String name = application.getFunctionSymbol().getName();

        visitor.getPrinter().append(prettyPrintSubscriptString(name));
    }

    @Override
    public void print(VariableTerm variable, PrettyPrintVisitor visitor) {
        String name = variable.getName();

        visitor.getPrinter().append(prettyPrintSubscriptString(name));
    }

    private String prettyPrintSubscriptString(String termRep) {
        Pattern pattern = Pattern.compile(SUBSCRIPT_PATTERN);
        Matcher matcher = pattern.matcher(termRep);
        StringBuilder sb = new StringBuilder("");

        List<String> indices = new ArrayList<>();

        String inner = "";

        int level = 0;
        while (matcher.matches()) {
            String index = matcher.group(2);
            StringBuilder indexBuilder = new StringBuilder("");
            for (int i = 0; i < index.length(); i++) {
                indexBuilder.append((char) (SUBSCRIPT_BASE + index.charAt(i) - '0'));
            }
            indices.add(level, indexBuilder.toString());
            inner = matcher.group(1);
            matcher = pattern.matcher(inner);
            level++;
        }

        if (level == 0) {
            // This should never happen!
            Logger.getGlobal().info("Could not PrettyPrint Term: " + termRep + ". With " + this.getClass());
            return termRep;
        }

        sb.append("(".repeat(level - 1));

        sb.append(inner);

        for (int i = 0; i < level -1; i++) {
            sb.append(indices.get(i));
            sb.append(")");
        }

        sb.append(indices.get(level - 1));

        return sb.toString();
    }

}
