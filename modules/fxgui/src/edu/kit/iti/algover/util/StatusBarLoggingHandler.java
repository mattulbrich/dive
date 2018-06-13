package edu.kit.iti.algover.util;

import com.sun.media.jfxmedia.logging.Logger;
import edu.kit.iti.algover.AlgoVerApplication;
import javafx.css.PseudoClass;
import org.controlsfx.control.StatusBar;

import java.util.ArrayList;
import java.util.List;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.LogRecord;

/**
 * Created by jklamroth on 4/24/18.
 */
public class StatusBarLoggingHandler extends Handler {
    private final StatusBar statusBar;
    private List<String> history;

    public StatusBarLoggingHandler(StatusBar statusBar) {
        this.statusBar = statusBar;
        this.history = new ArrayList<>();
        statusBar.getStylesheets().add(AlgoVerApplication.class.getResource("style.css").toExternalForm());
        statusBar.getStyleClass().add("log");
    }

    @Override
    public void publish(LogRecord record) {
        statusBar.setText(record.getMessage());
        setPseudoClassStateFromBranches(record.getLevel());
        history.add(record.getMessage());
    }

    @Override
    public void flush() {
    }

    @Override
    public void close() throws SecurityException {
    }

    private void setPseudoClassStateFromBranches(Level logLvl) {
        if (logLvl.equals(Level.SEVERE)) {
            statusBar.pseudoClassStateChanged(PseudoClass.getPseudoClass("error"), true);
            statusBar.pseudoClassStateChanged(PseudoClass.getPseudoClass("warning"), false);
            statusBar.pseudoClassStateChanged(PseudoClass.getPseudoClass("info"), false);
        } else if (logLvl.equals(Level.WARNING)) {
            statusBar.pseudoClassStateChanged(PseudoClass.getPseudoClass("error"), false);
            statusBar.pseudoClassStateChanged(PseudoClass.getPseudoClass("warning"), true);
            statusBar.pseudoClassStateChanged(PseudoClass.getPseudoClass("info"), false);
        } else {
            statusBar.pseudoClassStateChanged(PseudoClass.getPseudoClass("error"), false);
            statusBar.pseudoClassStateChanged(PseudoClass.getPseudoClass("warning"), false);
            statusBar.pseudoClassStateChanged(PseudoClass.getPseudoClass("info"), true);
        }
    }

    public List<String> getHistory() {
        return history;
    }

    public List<String> getHistory(int i) {
        if (history.size() >= 5) {
            return history.subList(history.size() - i - 1, history.size() - 1);
        }
        return history;
    }
}
