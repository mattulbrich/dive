/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
/*
 * This file is part of
 *    ivil - Interactive Verification on Intermediate Language
 *
 * Copyright (C) 2009-2012 Karlsruhe Institute of Technology
 *
 * The system is protected by the GNU General Public License.
 * See LICENSE.TXT (distributed with this file) for details.
 */
package edu.kit.iti.algover.swing;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;
import java.util.prefs.BackingStoreException;
import java.util.prefs.Preferences;

import javax.swing.JOptionPane;
import javax.swing.SwingUtilities;

import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.swing.actions.io.RecentProblemsMenu;
import edu.kit.iti.algover.swing.util.InputHistory;
import edu.kit.iti.algover.swing.util.Log;
import edu.kit.iti.algover.swing.util.Settings;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.Util;
import nonnull.NonNull;
import nonnull.Nullable;
import edu.kit.iti.algover.util.CommandLine;

/**
 * Main entry point for the GUI application.
 *
 * Reads arguments from command line, but checks also for other resources where
 * properties may have been set.
 *
 * <h2>Command line options</h2> See method {@link #makeCommandLine()} for all
 * command line options or run the program using the <code>-help</code> option.
 *
 */

public class Main {

    private static final String CMDLINE_CONFIG = "-config";
    private static final String CMDLINE_HELP = "-help";
    private static final String CMDLINE_PROOF = "-proof";
    private static final String CMDLINE_SAMPLES = "-samples";
    private static final String CMDLINE_LAST = "-last";

    private static Settings settings = Settings.getInstance();

    private static StartupWindow startupWindow;

    private static final String VERSION_PATH = "/META-INF/VERSION";

    private static final List<DiveCenter> PROOF_CENTERS = new LinkedList<DiveCenter>();

    /**
     * the number of recent files which are stored in the preferences and shown
     * in the menu.
     */
    private static final int NUMBER_OF_RECENT_FILES = 10;

    private static final InputHistory INPUT_HISTORY = new InputHistory("termInput", 20);

    private static final String ASSERTION_PROPERTY = "dive.enableAssertions";

    /*
     * - setup the settings from default resource, file and command line.
     * - set assertion state accordingly
     * - set directories accordingly
     */
    static {
        ClassLoader.getSystemClassLoader().setDefaultAssertionStatus(settings.getBoolean(ASSERTION_PROPERTY, true));
        // needed for the dummy-url "none:built-in", "buffer"
        // Util.registerURLHandlers();

        String antialiasing = settings.getProperty("dive.antialias", "gasp");
        System.setProperty("awt.useSystemAAFontSettings", antialiasing);
    }

    public static void main(final String[] args) {

        SwingUtilities.invokeLater(new Runnable() {
            @Override
            public void run() {
                try {
                    printVersion();

                    CommandLine commandLine = makeCommandLine();
                    commandLine.parse(args);

                    if(commandLine.isSet(CMDLINE_HELP)) {
                        commandLine.printUsage(System.out);
                        System.exit(0);
                    }

                    if(commandLine.isSet(CMDLINE_CONFIG)) {
                        Properties p = new Properties();
                        p.load(new FileReader(commandLine.getString(CMDLINE_CONFIG, "")));
                        Settings.getInstance().putAll(p);
                    }

                    List<String> fileArguments = commandLine.getArguments();

                    if(commandLine.isSet(CMDLINE_LAST)) {
                        // -last
                        String mostRecentProblem = RecentProblemsMenu.getMostRecentProblem();
                        if(mostRecentProblem != null) {
                            openDiveCenter(new File(mostRecentProblem));
                        }

                    } else if(fileArguments.isEmpty()) {
                        // no file args
                        startupWindow = new StartupWindow();
                        startupWindow.setVisible(true);
                        if(commandLine.isSet(CMDLINE_SAMPLES)) {
                            startupWindow.showSampleBrowser();
                        }
                    } else {

                        // at least one file/url arg
                        File file = new File(fileArguments.get(0));
                        openDiveCenter(file);
                    }
                } catch (Throwable ex) {
                    Log.log(Log.ERROR, "Exception during startup: " + ex.getMessage());
                    Log.stacktrace(ex);
                    System.exit(1);
                }
            }
        });
    }

    private static void printVersion() {
        String version = "<unknown version>";
        try {
            URL resource = Main.class.getResource(VERSION_PATH);
            if (resource != null) {
                version = Util.readURLAsString(resource);
            }
        } catch (IOException ex) {
            ex.printStackTrace();
        }
        System.out.println("This is DIVE - " + version);
    }

    private static CommandLine makeCommandLine() {
        CommandLine cl = new CommandLine();
        cl.addOption(CMDLINE_HELP, null, "Print usage");
        cl.addOption(CMDLINE_CONFIG, "file", "Read configuration from a file overwriting defaults.");
        cl.addOption(CMDLINE_PROOF, "file", "Load proof from this file.");
        cl.addOption(CMDLINE_SAMPLES, null, "Open the sample browser");
        cl.addOption(CMDLINE_LAST, null, "Reload the most recent problem");
        return cl;
    }

    /**
     * adds a problem's URL to recent files; should be called after successfully
     * loading a problem. adding an url twice will remove the older duplicate;
     * if more then 10 entries are in the recent list, the oldest one will
     * perish
     *
     * @param file
     *            location of the problem file
     */
    private static void addToRecentProblems(@NonNull File file) {
        Preferences prefs = Preferences.userNodeForPackage(Main.class);
        String recent[] = prefs.get("recent problems", "").split("\n");
        List<String> newRecent = new ArrayList<String>(recent.length+1);

        String toAdd = file.toString();
        newRecent.add(toAdd);

        // add old recent files w/o the parameter
        for (int i = 0; i < recent.length &&
                newRecent.size() < NUMBER_OF_RECENT_FILES; i++) {

            if (!toAdd.equals(recent[i])) {
                newRecent.add(recent[i]);
            }
        }

        assert newRecent.size () <= NUMBER_OF_RECENT_FILES;

        String prefString = Util.join(newRecent, "\n");
        prefs.put("recent problems", prefString);

        try {
            prefs.flush();
        } catch (BackingStoreException e) {
            // this is quite an unimportant error. ... Only log it.
            Log.log(Log.ERROR, "Could not store away the list of recently opened files.", e);
        }
    }

    public static void closeDiveCenter(DiveCenter diveCenter) {
        assert PROOF_CENTERS.contains(diveCenter);

        diveCenter.properties().terminated.fire(true);

        PROOF_CENTERS.remove(diveCenter);

        if (PROOF_CENTERS.isEmpty()) {
            exit(0);
        }
    }

    public static void openDiveCenter(File file) throws DafnyParserException, FormatException, IOException {
        DiveCenter center = new DiveCenter(file);
        if (startupWindow != null) {
            startupWindow.dispose();
        }
        center.activate();
        addToRecentProblems(file);
        PROOF_CENTERS.add(center);
    }

    public static void exit(int exitValue) {
        INPUT_HISTORY.saveToPreferences();
        System.exit(exitValue);
    }

    public static InputHistory getTermInputHistory() {
        return INPUT_HISTORY;
    }

    /**
     * check whether at least one open proof center or one editor
     * has unsaved changes
     * @return true iff there are changes in one window
     */
    public static boolean windowsHaveChanges() {
        for (DiveCenter pc : PROOF_CENTERS) {
            if (pc.properties().unsavedChanges.getValue() == Boolean.TRUE) {
                return true;
            }
        }
        return false;
    }


}