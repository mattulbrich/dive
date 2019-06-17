/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing.util;

import java.awt.*;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;

import javax.swing.*;
import javax.swing.text.BadLocationException;

import nonnull.NonNull;
import nonnull.Nullable;

public class GUIUtil {

    private GUIUtil() {
        // hide constructor
    }

    /**
     * <p>
     * Certain characters have special significance in HTML, and should be
     * represented by HTML entities if they are to preserve their meanings. This
     * function returns a string with some of these conversions made.
     * </p>
     *
     * <p>
     * The translations performed are:
     * </p>
     * <ul>
     * <li>'&amp;' (ampersand) becomes '&amp;amp;'</li>
     * <li>'"' (double quote) becomes '&amp;quot;'</li>
     * <li>'&lt;' (less than) becomes '&amp;lt;'</li>
     * <li>'&gt;' (greater than) becomes '&amp;gt;'</li>
     * </ul>
     *
     * @param message
     *            The string which has to be translated.
     * @return The message string with the special html characters masked.
     */
    public static @NonNull String htmlentities(@NonNull String message) {
        message = message.replace("&", "&amp;");
        message = message.replace("<", "&lt;");
        message = message.replace(">", "&gt;");
        message = message.replace("\"", "&quot;");
        return message;
    }

    /**
     * An icon which can be used instead an image if the image cannot be loaded.
     * <p>When drawn it shows the string "??".
     */
    public static final Icon UNKNOWN_ICON = new Icon() {

        @Override
        public int getIconHeight() {
            return 16;
        }

        @Override
        public int getIconWidth() {
            return 16;
        }

        @Override
        public void paintIcon(Component c, Graphics g, int x, int y) {
            g.setColor(Color.red);
            g.drawString("??", x, y + 16);
        }

    };


    /**
     * Convenience method to create an icon.
     *
     * If the argument is null or the resource cannot be loaded, a bogus icon is
     * returned.
     *
     * @param resource
     *                the resource to load from
     *
     * @return a freshly created icon
     */
    public static @NonNull Icon makeIcon(@Nullable URL resource) {
        try {
            if (resource != null) {
                return new ImageIcon(resource);
            }
        } catch (Exception e) {
            e.printStackTrace();
        }

        Log.log(Log.WARNING, "Cannot load icon " + resource
                + ", continuing anyway ...");
        return UNKNOWN_ICON;
    }


    /**
     * Drain an input stream to an output stream.
     *
     * Read bytes from the input stream and dump them to the output stream as long as
     * more data is available.
     *
     * @param is
     *            the source to be drained
     * @param os
     *            the sink to drain to
     * @throws IOException
     *             Signals that an I/O exception has occurred.
     */
    public static void drainStream(InputStream is, OutputStream os) throws IOException {
        byte[] buffer = new byte[4096];
        int read = 0;
        while((read = is.read(buffer)) > 0) {
            os.write(buffer, 0, read);
        }
    }

    /**
     * Drain an input stream to a string.
     *
     * Read bytes from the input stream and dump them to a string which is then returned.
     *
     * @param is
     *            the source to be drained
     * @throws IOException
     *             Signals that an I/O exception has occurred.
     */
    public static String drainStream(InputStream is) throws IOException {
        byte[] buffer = new byte[4096];
        StringBuilder result = new StringBuilder();
        int read = 0;
        while((read = is.read(buffer)) > 0) {
            result.append(new String(buffer, 0, read));
        }
        return result.toString();
    }


    public static <T> T findComponent(Component c, Class<T> clss) {
        if (clss.isInstance(c)) {
            return clss.cast(c);
        } else {
            if (c instanceof Container) {
                Container container = (Container) c;
                for (int i = 0; i < container.getComponentCount(); i++) {
                    T res = findComponent(container.getComponent(i), clss);
                    if (res != null) {
                        return res;
                    }
                }
            }
            return null;
        }
    }

    /**
     * Get the position of a character in a text component based on 1-based
     * line and column indices.
     *
     * @param text the text into which to refer
     * @param line a line, 1 is the first line. Must be within the text
     * @param column a column, 1 is the first column.
     * @return the linear position of line/column within text.
     */
    public static int linecolToPos(JTextArea text, int line, int column) {
        try {
            return text.getLineStartOffset(line - 1) + column - 1;
        } catch (BadLocationException e) {
            Log.log(Log.WARNING, "Flaw in text area index computation");
            Log.stacktrace(Log.WARNING, e);
            return 0;
        }
    }
}
