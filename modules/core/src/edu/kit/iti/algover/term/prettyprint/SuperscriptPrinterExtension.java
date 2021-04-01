package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;

import java.util.HashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class SuperscriptPrinterExtension implements PrettyPrintExtension {

    private static final String SUPERSCRIPT_PATTERN = "(.*)#([0-9]+)(.*)";
    private static final Map<Character, Character> SUPERSCRIPT_CHAR = new HashMap<>() {{
        put('1', '\u00B9');
        put('2', '\u00B2');
        put('3', '\u00B3');
        put('4', '\u2074');
        put('5', '\u2076');
        put('6', '\u2076');
        put('7', '\u2077');
        put('8', '\u2078');
        put('9', '\u2079');
    }};

    @Override
    public boolean canPrint(FunctionSymbol functionSymbol) {
        return functionSymbol.getArity() == 0
                && functionSymbol.getName().matches(SUPERSCRIPT_PATTERN);
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
        Matcher matcher = Pattern.compile(SUPERSCRIPT_PATTERN).matcher(name);
        if (matcher.matches()) {
            StringBuilder sb = new StringBuilder(matcher.group(1));
            String index = matcher.group(2);
            for (int i = 0; i < index.length(); i++) {
                sb.append(SUPERSCRIPT_CHAR.get(index.charAt(i)));
            }
            sb.append(matcher.group(3));

            visitor.getPrinter().append(sb.toString());
        } else {
            // This should never happen!
            // TODO Add logging
            visitor.getPrinter().append(name);
        }
    }

}
