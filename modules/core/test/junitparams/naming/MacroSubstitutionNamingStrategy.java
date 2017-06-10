package junitparams.naming;

import junitparams.internal.Utils;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Locale;
import java.util.regex.Pattern;

public class MacroSubstitutionNamingStrategy implements TestCaseNamingStrategy {
    private static final String MACRO_PATTERN = "\\{[^\\}]{0,50}\\}";
    // Pattern that keeps delimiters in split result
    private static final Pattern MACRO_SPLIT_PATTERN = Pattern.compile(String.format("(?=%s)|(?<=%s)", MACRO_PATTERN, MACRO_PATTERN));
    private static final String MACRO_START = "{";
    private static final String MACRO_END = "}";
    static final String DEFAULT_TEMPLATE = "{method}({params}) [{index}]";
    private static final String[] DEFAULT_TEMPLATE_PARTS = MACRO_SPLIT_PATTERN.split(DEFAULT_TEMPLATE);

    private String[] templateParts;
    private String methodName;

    public MacroSubstitutionNamingStrategy(TestCaseName testCaseName, String methodName) {
        this.templateParts = MACRO_SPLIT_PATTERN.split(getTemplate(testCaseName));
        this.methodName = methodName;
    }

    public static String getTemplate(TestCaseName testCaseName) {
        if (testCaseName != null) {
            return testCaseName.value();
        }

        return DEFAULT_TEMPLATE;
    }

    @Override
    public String getTestCaseName(int parametersIndex, Object parameters) {
        String builtName = buildNameByTemplate(templateParts, parametersIndex, parameters);

        if (builtName.trim().isEmpty()) {
            return buildNameByTemplate(DEFAULT_TEMPLATE_PARTS, parametersIndex, parameters);
        } else {
            return builtName;
        }
    }

    private String buildNameByTemplate(String[] parts, int parametersIndex, Object parameters) {
        StringBuilder nameBuilder = new StringBuilder();

        for (String part : parts) {
            String transformedPart = transformPart(part, parametersIndex, parameters);
            nameBuilder.append(transformedPart);
        }

        return nameBuilder.toString();
    }

    private String transformPart(String part, int parametersIndex, Object parameters) {
        if (isMacro(part)) {
            return lookupMacroValue(part, parametersIndex, parameters);
        }

        return part;
    }

    private String lookupMacroValue(String macro, int parametersIndex, Object parameters) {
        String macroKey = getMacroKey(macro);

        switch (Macro.parse(macroKey)) {
            case INDEX: return String.valueOf(parametersIndex);
            case PARAMS: return Utils.stringify(parameters);
            case METHOD: return methodName;
            default: return substituteDynamicMacro(macro, macroKey, parameters);
        }
    }

    private String substituteDynamicMacro(String macro, String macroKey, Object parameters) {
        if (isMethodParameterIndex(macroKey)) {
            int index = parseIndex(macroKey);
            return Utils.getParameterStringByIndexOrEmpty(parameters, index);
        }

        return macro;
    }

    private boolean isMethodParameterIndex(String macroKey) {
        return macroKey.matches("\\d+");
    }

    private int parseIndex(String macroKey) {
        return Integer.parseInt(macroKey);
    }

    private String getMacroKey(String macro) {
        return macro
                .substring(MACRO_START.length(), macro.length() - MACRO_END.length())
                .toUpperCase(Locale.ENGLISH);
    }

    private boolean isMacro(String part) {
        return part.startsWith(MACRO_START) && part.endsWith(MACRO_END);
    }

    private enum Macro {
        INDEX,
        PARAMS,
        METHOD,
        NONE;

        public static Macro parse(String value) {
            if (macros.contains(value)) {
                return Macro.valueOf(value);
            } else {
                return Macro.NONE;
            }
        }

        private static final HashSet<String> macros = new HashSet<String>(Arrays.asList(
                Macro.INDEX.toString(), Macro.PARAMS.toString(), Macro.METHOD.toString())
        );
    }
}
