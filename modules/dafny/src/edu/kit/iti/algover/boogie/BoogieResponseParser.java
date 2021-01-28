package edu.kit.iti.algover.boogie;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class BoogieResponseParser {

    public static final Pattern ERROR_MSG_BP5003 = Pattern.compile(".*\\((\\d+),1\\): Error BP5003: A postcondition might not hold on this return path.");
    public static final String VERIFIER_FINISHED = "Boogie program verifier finished with (\\d+) verified, (\\d+) error";
    public List<Integer> procedureStarts = new ArrayList<>();
    public List<Integer> failedProcedures = new ArrayList<>();
    private boolean consistent;

    public BoogieResponseParser(String boogieCode) {
        int lineno = BoogieTranslation.PRELUDE_LINE_COUNT + 1;
        for (String line : boogieCode.split("\n")) {
            if (line.startsWith("procedure ")) {
                procedureStarts.add(lineno);
            }
            lineno ++;
        }
    }

    public void readFrom(InputStream in) throws IOException {
        consistent = false;
        try(BufferedReader br = new BufferedReader(new InputStreamReader(in))) {
            String line;
            while ((line = br.readLine()) != null) {
                if (BoogieProcess.VERBOSE_BOOGIE) {
                    System.out.println(" Boogie > " + line);
                }
                Matcher m = ERROR_MSG_BP5003.matcher(line);
                if (m.matches()) {
                    failedProcedures.add(getProcedureForLine(Integer.parseInt(m.group(1))));
                }

                m = Pattern.compile(VERIFIER_FINISHED).matcher(line);
                if (m.find()) {
                    // Number of procs must be right and number of errors
                    int verified = Integer.parseInt(m.group(1));
                    int errors = Integer.parseInt(m.group(2));
                    if (procedureStarts.size() == verified + errors && failedProcedures.size() == errors) {
                        consistent = true;
                        return;
                    }
                }
            }
        }
    }

    private int getProcedureForLine(int line) {
        for (int idx = procedureStarts.size()-1; idx >= 0; idx--) {
            if (line >= procedureStarts.get(idx)) {
                return idx;
            }
        }
        throw new RuntimeException("This should not be reached");
    }

    public boolean isConsistent() {
        return consistent;
    }

    public List<Integer> getFailedProcedures() {
        return failedProcedures;
    }

    public Collection<Integer> getVerifiedProcedures() {
        List<Integer> result = new ArrayList<>();
        for (int i = 0; i < procedureStarts.size(); i++) {
            if (!failedProcedures.contains(i)) {
                result.add(i);
            }
        }
        return result;
    }
}
