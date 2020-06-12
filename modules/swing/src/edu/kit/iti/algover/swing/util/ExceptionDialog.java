/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

/*
 * this class has originally been written for "verbtrainer"
 */

package edu.kit.iti.algover.swing.util;

import java.awt.Dimension;
import java.awt.EventQueue;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.Window;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.PrintWriter;
import java.io.StringWriter;

import javax.swing.BoxLayout;
import javax.swing.Icon;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JToggleButton;
import javax.swing.UIManager;

/*
 * This code was edited or generated using CloudGarden's Jigloo SWT/Swing GUI
 * Builder, which is free for non-commercial use. If Jigloo is being used
 * commercially (ie, by a corporation, company or business for any purpose
 * whatever) then you should purchase a license for each developer using Jigloo.
 * Please visit www.cloudgarden.com for details. Use of Jigloo implies
 * acceptance of these licensing terms. A COMMERCIAL LICENSE HAS NOT BEEN
 * PURCHASED FOR THIS MACHINE, SO JIGLOO OR THIS CODE CANNOT BE USED LEGALLY FOR
 * ANY CORPORATE OR COMMERCIAL PURPOSE.
 */

/**
 * A dialog which shows an exception message and allows one to expand a pane that
 * then contains the stacktrace.
 *
 * @author mattias ulbrich
 */
public class ExceptionDialog extends JDialog {
    private static final long serialVersionUID = -3300467843405170589L;

    /**
     * Minimum width of the dialog.
     */
    private static final int MIN_WIDTH = 300;

    /**
     * How many characters per line for exception messages
     */
    private static final int LINE_LENGTH = 72;

    /**
     * Maximum number of lines before a truncation message is displayed.
     */
    private static final int MAX_LINES = 32;

    /**
     * Icon to display in dialog.
     */
    private static final Icon ERROR_ICON = UIManager.getIcon("OptionPane.ERROR_ICON");

    /**
     * text area that holds the stacktrace
     */
    private JTextArea jTextArea;

    /**
     * container for jTextArea
     */
    private JScrollPane jScrollPane;

    /**
     * Button "Details"
     */
    private JToggleButton jDetails;

    /**
     * The exception to display, can be null.
     */
    private final Throwable exception;

    /**
     * Error message to display
     */
    private String message;

    /**
     * Remembering initial size of the dlg.
     */
    private final Dimension firstSize;

    /**
     * One can set an alternative button label
     */
    private final String alternateButtonText;

    /**
     * remember triggering the alternate button
     */
    private boolean alternateHasBeenPressed;

    /*
     * private constructor invoked from {@link #showExceptionDialog(Window, String)}
     */
    private ExceptionDialog(Window w, String message, Throwable throwable, String alternateButton) {
        super(w, "Error", ModalityType.APPLICATION_MODAL);
        this.exception = throwable;
        this.message = message;
        this.alternateButtonText = alternateButton;
        initGUI();
        firstSize = getSize();
    }

    private void initGUI() {
        {
            GridBagLayout thisLayout = new GridBagLayout();
            thisLayout.columnWidths = new int[] { 0, MIN_WIDTH };
            getContentPane().setLayout(thisLayout);
            this.setSize(282, 195);
            {
                JLabel jIcon = new JLabel();
                getContentPane().add(
                        jIcon,
                        new GridBagConstraints(0, 0, 1, 1, 0.0, 0.0,
                                GridBagConstraints.CENTER,
                                GridBagConstraints.NONE, new Insets(20, 20, 10,
                                        10), 0, 0));
                jIcon.setIcon(ERROR_ICON);
            }
            {
                JComponent jError = mkErrorPanel();
                getContentPane().add(
                        jError,
                        new GridBagConstraints(1, 0, 1, 1, 1.0, 0.0,
                                GridBagConstraints.CENTER,
                                GridBagConstraints.BOTH, new Insets(20, 10, 10,
                                        20), 0, 0));
                // jError.setHorizontalAlignment(SwingConstants.CENTER);
                // jError.setHorizontalTextPosition(SwingConstants.CENTER);
            }
            {
                JPanel jPanel1 = new JPanel();
                getContentPane().add(
                        jPanel1,
                        new GridBagConstraints(0, 1, 2, 1, 0.0, 0.0,
                                GridBagConstraints.EAST,
                                GridBagConstraints.NONE,
                                new Insets(0, 0, 0, 0), 0, 0));
                {
                    jDetails = new JToggleButton();
                    jPanel1.add(jDetails);
                    jDetails.setText("Details ...");
                    jDetails.addActionListener(new ActionListener() {
                        @Override
                        public void actionPerformed(ActionEvent evt) {
                            jDetailsActionPerformed(evt);
                        }
                    });
                }
                if(alternateButtonText != null) {
                    JButton jAlternate = new JButton();
                    jAlternate.setText(alternateButtonText);
                    jAlternate.addActionListener(new ActionListener() {
                        @Override
                        public void actionPerformed(ActionEvent e) {
                            alternateHasBeenPressed = true;
                            setVisible(false);
                        }
                    });
                    jPanel1.add(jAlternate);
                }
                {
                    JButton jOK = new JButton();
                    jPanel1.add(jOK);
                    jOK.setText("Close");
                    jOK.addActionListener(new ActionListener() {
                        @Override
                        public void actionPerformed(ActionEvent evt) {
                            setVisible(false);
                        }
                    });
                    getRootPane().setDefaultButton(jOK);
                }
            }
            {
                jScrollPane = new JScrollPane();
                {
                    jTextArea = new JTextArea();
                    jTextArea.setEditable(false);
                    jTextArea.setTabSize(1);
                    jScrollPane.setViewportView(jTextArea);
                }
            }
        }
        pack();
    }

    private boolean isAlternatePressed() {
        return alternateHasBeenPressed;
    }

    private void jDetailsActionPerformed(ActionEvent evt) {
        if (jDetails.isSelected()) {
            getContentPane().add(
                    jScrollPane,
                    new GridBagConstraints(0, 2, 2, 1, 0.0, 1.0,
                            GridBagConstraints.CENTER, GridBagConstraints.BOTH,
                            new Insets(10, 10, 10, 10), 0, 0));
            StringWriter out = new StringWriter();
            PrintWriter pw = new PrintWriter(out);
            exception.printStackTrace(pw);
            verboseTrace(exception, pw);

            jTextArea.setText(out.toString());
            // jTextArea.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
            setSize(new Dimension(firstSize.width, firstSize.height * 2));
        } else {
            getContentPane().remove(jScrollPane);
            pack();
            setSize(firstSize);
        }
    }

    private void verboseTrace(Throwable throwable, PrintWriter pw) {
        if(throwable == null) {
            return;
        }

        /*if (throwable instanceof CompoundException) {
            CompoundException compEx = (CompoundException) throwable;
            for (Exception ex : compEx) {
                Log.stacktrace(ex);
                pw.println("--- EMBEDDED EXCEPTION");
                ex.printStackTrace(pw);
                verboseTrace(ex, pw);
            }
        }
        */
        verboseTrace(throwable.getCause(), pw);
    }

    // from BasicOptionPaneUI.
    /**
     * Recursively creates new JLabel instances to represent <code>d</code>.
     * Each JLabel instance is added to <code>c</code>.
     */
    private JComponent mkErrorPanel() {
        // Primitive line wrapping

        if (message == null) {
            return new JLabel("");
        }

        if (message.length() <= LINE_LENGTH) {
            return new JLabel(message);
        }

        JPanel panel = new JPanel();
        panel.setLayout(new BoxLayout(panel, BoxLayout.Y_AXIS));

        while (message.length() > LINE_LENGTH) {
            int p = message.lastIndexOf(' ', LINE_LENGTH);
            if (p <= 0) {
                p = message.indexOf(' ', LINE_LENGTH);
            }

            if (p > 0) {
                panel.add(new JLabel(message.substring(0, p)));
                if(panel.getComponentCount() > MAX_LINES) {
                    message = "[This message has been truncated]";
                } else {
                    message = message.substring(p + 1);
                }
            } else {
                panel.add(new JLabel(message));
                message = "";
            }
        }

        if (!message.trim().isEmpty()) {
            panel.add(new JLabel(message));
        }

        return panel;
    }

    /**
     * Show a modal exception dialog.
     *
     * @param parentComponent the window to relate this dialog to
     * @param throwable the thrown exception / throwable.
     */
    public static void showExceptionDialog(Window parentComponent,
            Throwable throwable) {
        showExceptionDialog(parentComponent, throwable.getLocalizedMessage(),
                throwable, null);
    }

    /**
     * Show a modal exception dialog.
     *
     * Stacktrace is taken from the current program location.
     *
     * @param parentComponent the window to relate this dialog to
     * @param message the error message
     */
    public static void showExceptionDialog(Window parentComponent, String message) {
        showExceptionDialog(parentComponent, new StackTraceThrowable(message));
    }

    /**
     * Show a modal exception dialog.
     *
     * The error message is taken from the message parameter whereas the stacktrace
     * comes from the throwable.
     *
     * @param parentComponent the window to relate this dialog to
     * @param message the error message
     * @param throwable the thrown exception / throwable.
     */
    public static void showExceptionDialog(Window parentComponent,
            String message, Throwable throwable) {
        showExceptionDialog(parentComponent, message, throwable, null);
    }

    /**
     * Show a modal exception dialog.
     *
     * Display a second button with an alternative action.
     *
     * @param parentComponent the window to relate this dialog to
     * @param message error message to display
     * @param alternateButton Text for the second button in the dialog, null for no such button.
     * @return true if the alternate button has been pressed
     */
    public static boolean showExceptionDialog(Window parentComponent, String message, String alternateButton) {
        return showExceptionDialog(parentComponent, new StackTraceThrowable(message), alternateButton);
    }

    /**
     * Show a modal exception dialog.
     *
     * The stacktrace is taken from the call location.
     * Display a second button with an alternative action.
     *
     * @param parentComponent the window to relate this dialog to
     * @param throwable the thrown exception / throwable.
     * @param alternateButton Text for the second button in the dialog, null for no such button.
     * @return true if the alternate button has been pressed
     */
    public static boolean showExceptionDialog(Window parentComponent,
                                              Throwable throwable, String alternateButton) {
        return showExceptionDialog(parentComponent, throwable.getLocalizedMessage(),
                throwable, alternateButton);
    }

    /**
     * Show a modal exception dialog.
     *
     * Display a second button with an alternative action.
     *
     * The error message is taken from the message parameter whereas the stacktrace
     * comes from the throwable.
     *
     * @param parentComponent the window to relate this dialog to
     * @param message error message to display
     * @param throwable the thrown exception / throwable.
     * @param alternateButton Text for the second button in the dialog, null for no such button.
     * @return true if the alternate button has been pressed
     */
    public static boolean showExceptionDialog(Window parentComponent,
                                              String message, Throwable throwable, String alternateButton) {
        Log.stacktrace(Log.DEBUG, throwable);

        if(Log.isLogging(Log.WARNING)) {
            if(!EventQueue.isDispatchThread()) {
                Log.log(Log.WARNING, "Show exception not on AWT thread, but on: " +
                        Thread.currentThread().getName());
            }
        }

        ExceptionDialog dlg = new ExceptionDialog(parentComponent, message,
                throwable, alternateButton);
        dlg.setLocationRelativeTo(parentComponent);
        dlg.setVisible(true);
        dlg.dispose();
        return dlg.isAlternatePressed();
    }

    @SuppressWarnings("checkstyle:MissingJavadocMethod")
    public static void main(String[] args) {
        showExceptionDialog(new JFrame(), new NullPointerException(
                "Some more eleborate error message"));
        showExceptionDialog(new JFrame(), "some other error");
        showExceptionDialog(new JFrame(), "message and exception", new Exception("this should not appear"));
        showExceptionDialog(
                new JFrame(),
                "ugly looooooooooong error with lots of details, for instance http://java.sun.com/j2se/1.4.2/docs/api/java/awt/GridBagLayout.html#columnWidths");
        showExceptionDialog(
                new JFrame(),
                "1234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890");
        showExceptionDialog(
                new JFrame(),
                "1234567890 1234567890 1234567890 1234567890 1234567890 1234567890 1234567890 1234567890 1234567890 1234567890");
        showExceptionDialog(
                new JFrame(),
                new Exception(
                "1234567890 1234567890 1234567890 1234567890 1234567890 1234567890 1234567890 1234567890 1234567890 1234567890"));

        System.out.println(showExceptionDialog(new JFrame(), "Message to display", "Extra Button"));
        System.out.println(showExceptionDialog(new JFrame(), "Message to display (2)", new RuntimeException("Exceptional text"), "Extra Button"));

        System.exit(0);
    }

    private static class StackTraceThrowable extends Throwable {

        private static final long serialVersionUID = 4003181857244674111L;

        public StackTraceThrowable(String message) {
            super(message);
        }

        @Override
        public void printStackTrace(PrintWriter s) {
            synchronized (s) {
                s.println("Stack Trace:");
                StackTraceElement[] trace = getStackTrace();
                for (int i = 1; i < trace.length; i++) {
                    s.println("\tat " + trace[i]);
                }
            }
        }
    }

}
