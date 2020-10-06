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

import java.awt.Color;
import java.awt.Font;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import nonnull.NonNull;

/**
 * Settings are "pimped {@link Properties}".
 *
 * Only they provide typed getter-methods.
 *
 * If a property is looked up, the order is the following:
 *
 * Defaults are read from the file <code>Settings_default.properties</code>.
 * <ol>
 * <li>the settings stored in the Settings_default.properties" file in the
 * resources
 * <li>the settings returned by System.getProperty (includes all -D...=...
 * commandline options!)
 * <li>the settings loaded/set by the program.
 * </ol>
 *
 * Settings are used for settings on a per-user level. Other info should be
 * stored in szenario files.
 *
 * Store results in caches for the conversion may be costly.
 *
 * For convenience also store all keys in here.
 *
 * This is a singleton.
 *
 * @author mattze
 */
public class Settings {

    /**
     * To avoid producing object multiple times, a cache saves them for later lookup.
     */
    private Map<String, Object> cache = new HashMap<String, Object>();

    /**
     * The properties that back this object up.
     */
    private Properties contents;

    /**
     * The singleton instance.
     */
    private static Settings theInstance = new Settings();

    /**
     * create the settings object. Load the defaults from the defaults file, add
     * load from the system directory file and the system properties.
     */
    private Settings() {
        super();
        try {
            contents = new Properties();
            InputStream stream = getClass().getResourceAsStream("/edu/kit/iti/algover/swing/Settings_default.properties");
            contents.load(stream);
            stream.close();
            contents.putAll(System.getProperties());
        } catch (Exception ex) {
            throw new RuntimeException("Cannot initialise Settings", ex);
        }
    }

    /**
     * Get the singleton instance of the Settings class.
     * <p>
     * The object is created at class loading time.
     * </p>
     * @return a non-null instance of Settings. The same on any invocation.
     */
    public static Settings getInstance() {
        return theInstance;
    }

    /**
     * store a single value into the settings.
     *
     * It is stored in the underlying properties.
     * @param key the key store under
     * @param value the string value to store
     * @return the previous value associated with key, or null if there was no mapping for key.
     */
    public synchronized Object put(@NonNull String key, @NonNull String value) {
        return contents.put(key, value);
    }

    /*
     * check the cache and return a cached element if there is one
     */
    private <T> T getCached(String key, Class<T> clss) {
        Object cached = cache.get(key);
        if(clss.isInstance(cache.get(key))) {
            return clss.cast(cached);
        } else {
            return null;
        }
    }

    private void putCache(String key, Object value) {
        assert value != null;
        cache.put(key, value);
    }

    /**
     * lookup a value in the properties and use its value as a class name and
     * create a new instance of that class
     *
     * @param key
     *            key for the classname
     * @return new instance of the class of that class name
     * @throws SettingsException instantiation failed
     */
    public Object createInstance(String key) throws SettingsException {
        try {
            Class<?> clss = getCached(key, Class.class);
            if(clss == null) {
                String value = getProperty(key);
                clss = Class.forName(value);
                putCache(key, clss);
            }
            return clss.getDeclaredConstructor().newInstance();
        } catch (Exception e) {
            throw new SettingsException("Cannot create class for key " + key, e);
        }
    }

    /**
     * Lookup an integer value in the properties.
     *
     * <p>
     * The number can be specified as decimal constant, octal or hexadecimal. It
     * accepts the same input as {@link Integer#decode(String)}, see there for
     * details.
     *
     * @see Integer#decode(String)
     * @param key      key to look up
     * @return integer value of the key's value
     *
     * @throws SettingsException
     *                 if the value does not represent an integer or
     *                 if the key has not been defined in these settings.
     */
    public int getInteger(String key) throws SettingsException {
        String value = getProperty(key);
        try {
            return Integer.decode(value);
        } catch (NumberFormatException e) {
            throw new SettingsException("Cannot create integer for key " + key, e);
        }
    }

    /**
     * Lookup an integer value in the properties.
     *
     * <p>
     * The number can be specified as decimal constant, octal or hexadecimal. It
     * accepts the same input as {@link Integer#decode(String)}, see there for
     * details.
     *
     * <p>The method returns a default value if the key is not present.</p>
     *
     * @see Integer#decode(String)
     * @param key      key to look up
     * @param defaultValue the value to return on case that key is not present in the settings
     * @return integer value of the key's value
     *
     * @throws SettingsException
     *                 if the value does not represent an integer or
     *                 if the key has not been defined in these settings.
     */
    public int getInteger(String key, int defaultValue) {
        try {
            return getInteger(key);
        } catch (SettingsException e) {
            // log
            Log.log(Log.VERBOSE, "Falling back to default value " + defaultValue);
            Log.stacktrace(Log.VERBOSE, e);
            return defaultValue;
        }
    }


    /**
     * Searches for the property with the specified key in this property list.
     * The method throws a
     * {@link SettingsException} if the key is not present in any property
     * list.
     *
     * @param key
     *                the property key.
     *
     * @return the value in this property list with the specified key value.
     *
     * @throws SettingsException
     *                 if key has not been defined
     */
    public String getProperty(@NonNull String key) throws SettingsException {
        if (!contents.containsKey(key))
            throw new SettingsException("No value for key " + key);

        return contents.getProperty(key);
    }

    /**
     * Searches for the property with the specified key in this property list.
     * The method returns a default value if the key is not present
     *
     * @param key
     *                the property key.
     * @param defaultValue
     *                the default value to return if the key is not present.
     *
     * @return the value in this property list with the specified key value.
     */
    public String getProperty(String key, String defaultValue) {
        try {
            return getProperty(key);
        } catch (SettingsException e) {
            // log
            Log.log(Log.VERBOSE, "Falling back to default value " + defaultValue);
            Log.stacktrace(Log.VERBOSE, e);
            return defaultValue;
        }
    }

    /**
     * Searches for the property with the specified key in this property list.
     *
     * The result is expanded before return. This means that any expression
     * {@code ${name}} is resolved by looking up name in these settings and
     * inlining their string.
     *
     * @param key
     *                the property key.
     *
     * @return the value in this property list with the specified key value.
     */
    public String getExpandedProperty(String key) throws SettingsException {
        return expandString(getProperty(key));
    }

    /**
     * Searches for the property with the specified key in this property list.
     * The method returns a default value if the key is not present.
     *
     * The result is expanded before return. This means that any expression
     * {@code ${name}} is resolved by looking up name in these settings and
     * inlining the string.
     *
     * @param key
     *                the property key.
     * @param defaultValue
     *                the default value to return if the key is not present.
     *
     * @return the value in this property list with the specified key value.
     */
    public String getExpandedProperty(String key, String defaultValue) {
        try {
            String value = getProperty(key);
            return expandString(value);
        } catch (SettingsException e) {
            Log.log(Log.VERBOSE, "Falling back to default value " + defaultValue);
            Log.stacktrace(Log.VERBOSE, e);
            return defaultValue;
        }
    }

    /*
     * replace every occurrence of "${xyz}" by the value stored for xyz.
     * Do not recurse, because this might go on infinitely.
     */
    private String expandString(String value) {
        StringBuilder result = new StringBuilder();
        int keyStart = -1;

        for(int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            switch (c) {
            case '$':
                if(i < value.length() - 1 && value.charAt(i+1) == '{' && keyStart == -1) {
                    keyStart = i + 2;
                    i++;
                } else {
                    if(keyStart == -1) {
                        result.append(c);
                    }
                }
                break;

            case '}':
                if(keyStart == -1) {
                    result.append(c);
                } else {
                    String key = value.substring(keyStart, i);
                    String expansion;
                    try {
                        expansion = getProperty(key);
                    } catch(SettingsException ex) {
                        // log
                        Log.log(Log.WARNING, "Cannot expand ${" + key + "}, no such key defined");
                        expansion = "";
                    }

                    result.append(expansion);
                    keyStart = -1;
                }
                break;

            default:
                if(keyStart == -1) {
                    result.append(c);
                }
                break;
            }
        }

        return result.toString();
    }

    /**
     * Searches for the property with the specified key in this property list.
     *
     * The value is obtained from the string at the key by splitting it at commas.
     *
     * @param key
     *                the property key.
     *
     * @return the value in this property list with the specified key value.
     */
    public String[] getStrings(String key) throws SettingsException {
        String value = getProperty(key);
        return value.split(", *");
    }

    /**
     * return the boolean property that is stored in key.
     * If there is no such property false is returned.
     *
     * @param key the key to lookup
     * @return true iff key stored and has the value "true"
     */
    public boolean getBoolean(String key) throws SettingsException {
        return "true".equalsIgnoreCase(getProperty(key));
    }

    /**
     * return the boolean property that is stored in key. If there is no such
     * property defValue is returned.
     *
     * @param key
     *            the key to lookup
     * @param defaultValue
     *            the default value to return if the key is not defined
     * @return true iff key stored and has the value "true"
     */
    public boolean getBoolean(String key, boolean defaultValue)  {
            try {
                return getBoolean(key);
            } catch (SettingsException e) {
                // log
                Log.log(Log.VERBOSE, "Falling back to default value");
                Log.stacktrace(Log.VERBOSE, e);
                return defaultValue;
            }
    }

    // @todo DOC throws!
    public double getDouble(String key) throws SettingsException {
        String value = getProperty(key);
        try {
            return Double.parseDouble(value);
        } catch (NumberFormatException e) {
            throw new SettingsException("Cannot create double value for key " + key, e);
        }
    }

    /**
     * Use the {@link ColorResolver} to resolve a color name or id.
     *
     * @param key
     *            key to look up
     * @return a Color object
     * @throws SettingsException
     */
    public @NonNull Color getColor(@NonNull String key) throws SettingsException {
        Color color = getCached(key, Color.class);
        if(color == null) {
            String prop = getExpandedProperty(key);
            color= ColorResolver.getInstance().resolve(prop);
            if(color == null) {
                throw new SettingsException(prop + " does not describe a valid color in key " + key);
            }
            putCache(key, color);
        }

        return color;
    }


    /**
     * Use the {@link ColorResolver} to resolve a color name or id.
     *
     * Return a default value in case the lookup fails.
     *
     * @param key
     *                key to look up
     * @param defaultColor
     *                return this value if the lookup fails.
     *
     * @return a Color object
     */
    public Color getColor(String key, Color defaultColor) {
        try {
            return getColor(key);
        } catch(SettingsException e) {
            // log
            Log.log(Log.VERBOSE, "Falling back to default value " + defaultColor);
            Log.stacktrace(Log.VERBOSE, e);
            return defaultColor;
        }
    }


    /**
     * get a Font object for a key.
     *
     * "Fontname, style, size" is the format. "Arial, PLAIN, 12" for instance.
     *
     * Styles are: PLAIN, BOLD, ITALIC, BOLD+ITALIC. (not ITALIC+BOLD)
     *
     * @param key
     *                key to look up
     *
     * @return a Font object
     *
     * @throws SettingsException
     *                 if there is no value for key or
     *                 if the font size is not correctly defined or
     *                 if the style string is illegal or
     *                 if the descriptor does not have exactly 3 parts.
     */
    public @NonNull Font getFont(@NonNull String key) throws SettingsException {
        Font font = getCached(key, Font.class);
        if(font == null) {
            String[] strings = getStrings(key);
            try {
                if(strings.length != 3)
                    throw new IllegalArgumentException("Font descriptions must have exactly 3 parts");

                String fontname = strings[0];
                int style = decodeStyle(strings[1]);
                int size = Integer.decode(strings[2]);
                if(size <= 0)
                    throw new NumberFormatException("Negative font size: " + size);
                font = new Font(fontname, style, size);
                putCache(key, font);
            } catch (RuntimeException e) {
                throw new SettingsException("Cannot create font for key " + key, e);
            }
        }

        return font;
    }

    /**
     * get a Font object for a key. Return a default font if the indicated
     * key is missing or the description is invalid.
     *
     * "Fontname, style, size" is the format. "Arial, PLAIN, 12" for instance.
     *
     * Styles are: PLAIN, BOLD, ITALIC, BOLD+ITALIC. (not ITALIC+BOLD)
     *
     * @param key
     *            key to look up
     * @param defaultFont
     *            the font object to return in case of an invalid description
     *            or an error.
     *
     * @return a Font object
     */
    public Font getFont(String key, Font defaultFont) {
        try {
            return getFont(key);
        } catch(SettingsException e) {
            // log
            Log.log(Log.VERBOSE, "Falling back to default value");
            Log.stacktrace(Log.VERBOSE, e);
            return defaultFont;
        }
    }

    private int decodeStyle(String string) {
        if (string.equals("PLAIN"))
            return Font.PLAIN;
        if (string.equals("BOLD"))
            return Font.BOLD;
        if (string.equals("ITALIC"))
            return Font.ITALIC;
        if (string.equals("BOLD+ITALIC"))
            return Font.ITALIC + Font.BOLD;

        throw new RuntimeException("No valid font style: " + string);
    }

    /**
     * once the command line args have been parsed we can now load the settings
     * to the defaults - not overwriting set arguments
     *
     * @throws IOException
     *             file not found or reading error
     */
//    public void loadFromSystemDirectory(String directoryKey, String fileName) throws IOException {
//        String dir = getProperty(directoryKey);
//        if(dir != null) {
//            File f = new File(dir, fileName);
//            if(f.canRead()) {
////            logger.fine("Load settings from system directory: " + f);
//                FileInputStream fileInputStream = new FileInputStream(f);
//
//                try {
//                    defaults.load(fileInputStream);
//                } finally {
//                    if(fileInputStream != null)
//                        fileInputStream.close();
//                }
//            }
//        }
//    }

    /**
     * Load properties from a file into the settings.
     *
     * <p>
     * The filename is obtained by querying the settings for the argument key.
     *
     * @throws IOException
     *                 if something goes wrong while reading properties or
     *                 resolving names.
     */
    public void loadKeyAsFile(String propertiesFileKey) throws IOException {
        String fileName;
        try {
            fileName = getExpandedProperty(propertiesFileKey);
        } catch (SettingsException e) {
            IOException ex = new IOException("No properties file defined for key " + propertiesFileKey);
            ex.initCause(e);
            throw ex;
        }

        FileInputStream fileInputStream = new FileInputStream(fileName);
        try {
            contents.load(fileInputStream);
        } finally {
            if(fileInputStream != null)
                fileInputStream.close();
        }
    }

    /**
     * Remove all entries from this settings object,
     */
    public void clear() {
        contents.clear();
    }

    /**
     * Add all entries from the argument to this object.
     *
     * @param properties another collection of properties
     */
    public void putAll(@NonNull Properties properties) {
        contents.putAll(properties);
    }
}
