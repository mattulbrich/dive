/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import edu.kit.iti.algover.nuscript.ScriptException;
import edu.kit.iti.algover.nuscript.ast.ScriptAST;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
import org.antlr.v4.runtime.misc.ParseCancellationException;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.InputMismatchException;
import java.util.List;

/**
 * A collection of diagnosis methods for exception handling. In particular for
 * presenting nice error messages.
 *
 * <p>
 * It allows you to extract from any (supported) type of exception an
 * object of type {@link ExceptionReportInfo} that contains details about
 * the exception and its location. Call {@link #extractReportInfo(Throwable)}
 * to obtain this info.
 *
 * <p>An easy to read and informtive error description can be constructed using
 * {@link #getNiceErrorMessage(Throwable)}. Use
 * {@link #printNiceErrorMessage(Throwable)} to direct it to System.err directly.
 *
 * @author Mattias Ulbrich
 */
public final class ExceptionDetails {

    private ExceptionDetails() {
        throw new Error("must not be instantiated");
    }

    public static final class ExceptionReportInfo {
        private String message = "unknown error";
        private String filename;
        private String locationString = "unknown location";
        private int line = -1;
        private int column = -1;
        private int length = 1;

        public String getMessage() {
            return message;
        }

        public String getFilename() {
            return filename;
        }

        public String getLocationString() {
            return locationString;
        }

        public int getLine() {
            return line;
        }

        public int getColumn() {
            return column;
        }

        public int getLength() {
            return length;
        }
    }

    public static final ExceptionReportInfo extractReportInfo(Throwable ex) {

        if(ex instanceof DafnyParserException) {
            DafnyParserException dpe = (DafnyParserException) ex;
            ExceptionReportInfo result = new ExceptionReportInfo();
            result.message = dpe.getErrorMessage();
            result.filename = dpe.getFilename();
            result.locationString = "file " + result.filename;
            result.line = dpe.getLine();
            // Columns in ANTLR 3 start at 0
            result.column = dpe.getColumn() + 1;
            result.length = dpe.getLength();
            return result;
        }

        if (ex instanceof DafnyException) {
            DafnyException dex = (DafnyException) ex;
            ExceptionReportInfo result = new ExceptionReportInfo();
            DafnyTree tree = dex.getTree();
            result.message = ex.getMessage();
            result.filename = tree.getFilename();
            if(result.filename != null) {
                result.locationString = "file " + result.filename;
            }
            Token token = tree.getStartToken();
            if(token != null) {
                result.line = token.getLine();
                // Columns in ANTLR 3 start at 0
                result.column = token.getCharPositionInLine() + 1;
                result.length = token.getText().length();
            }
            return result;
        }

        if (ex instanceof ParseCancellationException) {
            ParseCancellationException pex = (ParseCancellationException) ex;
            Throwable cause = pex.getCause();
            ExceptionReportInfo report = extractReportInfo(cause);
            // we are likely to have a better error message.
            if(!pex.getMessage().isEmpty()) {
                report.message = ex.getMessage();
            }
            return report;
        }

        if (ex instanceof RecognitionException) {
            RecognitionException rex = (RecognitionException) ex;
            ExceptionReportInfo result = new ExceptionReportInfo();
            result.message = rex.getMessage();
            result.line = rex.line;
            result.column = rex.c;
            if(rex.token != null) {
                result.length = rex.token.getText().length();
            }
            return result;
        }

        if (ex instanceof org.antlr.v4.runtime.RecognitionException) {
            org.antlr.v4.runtime.RecognitionException rex = (org.antlr.v4.runtime.RecognitionException) ex;
            ExceptionReportInfo result = new ExceptionReportInfo();
            result.message = rex.getMessage();
            extractLineAndColumn(rex.getOffendingToken(), result);
            if(rex.getOffendingToken() != null) {
                result.length = rex.getOffendingToken().getText().length();
            }
            return result;
        }

        if(ex instanceof ScriptException) {
            ScriptException sex = (ScriptException) ex;
            ExceptionReportInfo result = new ExceptionReportInfo();
            result.message = sex.getMessage();
            ScriptAST ast = sex.getScriptAST();
            if(ast != null) {
                result.line = ast.getBeginToken().getLine();
                result.column = ast.getBeginToken().getCharPositionInLine();
                result.length = ast.getEndToken().getStopIndex() -
                        ast.getBeginToken().getStartIndex();
            }
            return result;
        }

        // ... add other classes here!

        Throwable cause = ex.getCause();
        if(cause != null) {
            return extractReportInfo(cause);
        } else {
            ExceptionReportInfo result = new ExceptionReportInfo();
            result.message = ex.getMessage();
            return result;
        }

    }

    private static void extractLineAndColumn(org.antlr.v4.runtime.Token token, ExceptionReportInfo report) {
        report.line = token.getLine();
        report.column = token.getCharPositionInLine();
        if(token.getType() == -1) {
            report.line--;
        }
    }

    public static void printNiceErrorMessage(Throwable ex) {
        System.err.println(getNiceErrorMessage(ex));
    }

    public static CharSequence getNiceErrorMessage(Throwable ex) {
        return getNiceErrorMessage(extractReportInfo(ex));
    }

    private static CharSequence getNiceErrorMessage(ExceptionReportInfo report) {
        StringBuilder sb = new StringBuilder();
        sb.append("Exception in " + report.locationString + ":");
        if(report.line > 0) {
            sb.append(report.line + ":" + report.column + ":");
        }
        sb.append("\n" + report.message + "\n");
        try {
            if (report.filename != null && report.line > 0) {
                List<String> lines = Files.readAllLines(Paths.get(report.filename));
                String line = lines.get(report.line - 1);
                sb.append("\n").append(line).append("\n")
                  .append(Util.duplicate(" ", report.column - 1))
                  .append(Util.duplicate("^", report.length))
                  .append("\n");
            }
        } catch (Exception ex) {
            sb.append("(IO exception which accessing the sources.)\n");
        }

        return sb;
    }
}
