/*
 * This file is part of
 *    ivil - Interactive Verification on Intermediate Language
 *
 * Copyright (C) 2009-2012 Karlsruhe Institute of Technology
 *
 * The system is protected by the GNU General Public License.
 * See LICENSE.TXT (distributed with this file) for details.
 */
package edu.kit.iti.algover.swing.util;

/**
 * This exception is used by {@link Settings} to indicate problems while
 * retrieving setting contents.
 * 
 * Settings provides for most operations variants which do not throw exceptions
 * by diverge to a default value and merely print an error message.
 */
public class SettingsException extends Exception {

    private static final long serialVersionUID = -4030999051412153464L;

    public SettingsException() {
        super();
    }

    public SettingsException(String message, Throwable cause) {
        super(message, cause);
    }

    public SettingsException(String message) {
        super(message);
    }

    public SettingsException(Throwable cause) {
        super(cause);
    }

}
