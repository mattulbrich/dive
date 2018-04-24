package edu.kit.iti.algover.util;

import org.controlsfx.control.StatusBar;

import java.util.logging.Handler;
import java.util.logging.LogRecord;

/**
 * Created by jklamroth on 4/24/18.
 */
public class StatusBarLoggingHandler extends Handler {
    private final StatusBar statusBar;

    public StatusBarLoggingHandler(StatusBar statusBar) {
        this.statusBar = statusBar;
    }

    @Override
    public void publish(LogRecord record) {
        statusBar.setText(record.getMessage());
    }

    @Override
    public void flush() {
    }

    @Override
    public void close() throws SecurityException {
    }
}
