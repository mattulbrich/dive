/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing.actions;

import java.awt.Dimension;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.net.URL;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;

import javax.swing.Action;
import javax.swing.JButton;
import javax.swing.JCheckBoxMenuItem;
import javax.swing.JComponent;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JPopupMenu;
import javax.swing.JRadioButtonMenuItem;
import javax.swing.JSeparator;
import javax.swing.JToggleButton;
import javax.swing.JToolBar;
import javax.swing.KeyStroke;

import edu.kit.iti.algover.swing.util.GUIUtil;
import edu.kit.iti.algover.swing.util.Log;
import nonnull.NonNull;
import nonnull.Nullable;

/**
 * The Class BarManager is a pretty generic framework to allow menu bars and
 * tool bars to be configured via a <code>.properties</code> file declaring all
 * actions whose classes will then be loaded.
 *
 * <h2>The actions</h2>
 *
 * Actions can be both registered for toolbars and menu bars. There is at most
 * one object for a certain class within one bar manager. They are reused upon a
 * second registration.
 *
 * <p>
 * When an action is created, the created object is furnished with the default
 * properties first. If it also implements the interface
 * {@link Initialisable}, the initialised method is invoked, to give the
 * the action the opportunity to set itself up using the provided properties.
 *
 * <h2>The configuration</h2>
 *
 * Configuration has to be provided in a <code>.properties</code> file with the
 * following special keys:
 * <table border=1 cellspacing=5>
 * <tr>
 * <td><code>menubar</code></td>
 * <td>Key for the menubar</td>
 * <td>Listing all keys for top level menus in the bar in proper order</td>
 * </tr>
 * <tr>
 * <td><code>toolbar</code></td>
 * <td>Key for the toolbar</td>
 * <td>Listing all keys for all buttons the bar in proper order. You may use
 * <code>SEPARATOR</code> to create empty space between buttons.</td>
 * </tr>
 * <tr>
 * <td>menu (as appearing in menubar)</td>
 * <td>Key for a menu</td>
 * <td>Listing all keys for menu items in the menu in proper order. You may use
 * <code>SEPARATOR</code> to create a separating line between entries. An entry
 * for the subkey <code>.text</code> defines the title of the menu</td>
 * </tr>
 * <tr>
 * <td>item (as appearing in a menu/toolbar)</td>
 * <td>Definition of an action</td>
 * <td>Keyword and further information, see below</td>
 * </tr>
 * </table>
 *
 * <h3>Action Types</h3>
 *
 * <table border=1 cellspacing=5>
 * <tr>
 * <th>Keyword</th>
 * <th>Menu/Toolbar</th>
 * <th>Parameters</th>
 * <th>Expl.</th>
 * </tr>
 * <tr>
 * <td><code>ACTION</code></td>
 * <td>M/T</td>
 * <td>class name</td>
 * <td>create an action object of the given class name and add a button or menu
 * item for it</td>
 * </tr>
 * <tr>
 * <td><code>TOGGLE_ACTION</code></td>
 * <td>M/T</td>
 * <td>class name</td>
 * <td>create an action object of the given class name and add a toggle button
 * or checkable menu item for it</td>
 * </tr>
 * <tr>
 * <td><code>COMMAND</code></td>
 * <td>M/T</td>
 * <td>command string</td>
 * <td>create a button or menu item with the given command set as command. You
 * can use subkeys <code>.text</code>, <code>.icon</code> and
 * <code>.tooltip</code> to set the text for the button/menu or the resource for
 * the image.</td>
 * </tr>
 * <tr>
 * <td><code>TODO</code></td>
 * <td>M/T</td>
 * <td>Name</td>
 * <td>create a new deactivated button or menu item with the given title.
 * Placeholder for future functionality</td>
 * </tr>
 * <tr>
 * <td><code>SUBMENU</code></td>
 * <td>M/-</td>
 * <td>key</td>
 * <td>create a submenu and create it using the specified key</td>
 * </tr>
 * <tr>
 * <td><code>COMPONENT</code></td>
 * <td>M/T</td>
 * <td>class name</td>
 * <td>create an instance of the specified class which must extend
 * {@link JComponent}</td>
 * </tr>
 * </table>
 *
 * To faciliate the specification of classnames, you can provide a key
 * <code>package</code> into which all class names are assumed if they do not
 * contain a "." (dot). You can use "/" to indicate, that a class is in a sub
 * package of the default package.
 *
 * <h3>Example configuration</h3>
 * Here a small but typical example:
 *
 * <pre>
 * package = org.example.barmanager
 * menubar = fileMenu editorMenu helpMenu
 * toolbar = file.open SEPARATOR editor.paste
 *
 * fileMenu = file.open file.close SEPARATOR exit
 * editorMenu = editor.copy editor.cut editor.paste
 * helpMenu = help
 *
 * file.open = ACTION FileOpenAction
 * # ...
 *
 * editor.copy = COMMAND copy-to-clipboard
 * editor.copy.text = Copy
 * editor.copy.tooltip = Copy to clipboard
 * editor.copy.icon = img/copy.png
 * # ...
 *
 * help = help.index help.search
 * help.index = TODO Index
 * # ...
 * </pre>
 *
 * <h2>Example usage</h2>
 *
 * To create a bar manager do something like:
 *
 * <pre>
 * BarManager barManager = new BarManager(null, resource);
 * barManager.putProperty(PARENT_FRAME, jframe);
 * barManager.putProperty(SOME_PROP, somevalue);
 * jframe.setJMenuBar(barManager.makeMenubar());
 * </pre>
 *
 * <h2>Properties</h2>
 *
 * A BarManger is equipped with a properties mechanism. You can use the method
 * {@link #putProperty(String, Object)} to set a property (an arbitrary object).
 * These values will be transmitted to all created user specified actions and
 * components. <i>Please note: Properties set/changed after the creation of an
 * action are not retransmitted to the component.</i>
 */
public class BarManager {

    /**
     * An Action implementing this interface will have its initialised method
     * invoked if created by a bar manager. This invocation happens after all
     * properties have been set in the action, so that the information can be
     * used to set the action up.
     */
    public static interface Initialisable {

        /**
         * Implementing classes can provide code which sets up the action.
         * This method is invoked after all relevant properties have been set.
         */
        void initialised();
    }

    /**
     * The property name for the default menubar.
     */
//    private static final String DEFAULT_MENUBAR_PROPERTY = "menubar";

    /**
     * The property name for the default toolbar.
     */
//    private static final String DEFAULT_TOOLBAR_PROPERTY = "toolbar";

    /**
     * The general action listener which is set on all created buttons, menu
     * items, etc.
     */
    private final ActionListener actionListener;

    /**
     * The map of properties provided to the freshly created actions.
     */
    private final Map<String, Object> defaultActionProperties = new HashMap<String, Object>();

    /**
     * The properties with which the bar manager is configured
     */
    private Properties properties;

    /**
     * The resource from where the properties are read
     */
    private final URL resource;

    /**
     * The action cache stores all created objects so that objected created once
     * will be reused.
     */
    private final Map<String, Action> actionCache =
        new HashMap<String, Action>();

    /**
     * The package prefix if one is provided in the properties, null only in the
     * beginning
     */
    private String packagePrefix;

    /**
     * A flag to indicate whether toolbar buttons should have text or images
     * only.
     */
//    private boolean toolbarOnlyIcons;

    /**
     * Instantiates a new bar manager. The configuration is to be read from a
     * URL.
     *
     * @param actionListener
     *            the action listener
     * @param resource
     *            the resource
     */
    public BarManager(ActionListener actionListener, URL resource) {
        this.actionListener = actionListener;
        this.resource = resource;
    }

    /*
     * Prepare properties: load from URL, read package info, make flags.
     */
    private void prepareProperties() throws IOException {
        if(properties == null) {
            properties = NestedXMLPropertyReader.read(resource.openStream(), true);

            properties.put("SEPARATOR", "SEPARATOR");

            packagePrefix = properties.getProperty("package");
            if(packagePrefix == null) {
                packagePrefix = "";
            } else {
                packagePrefix = packagePrefix + ".";
            }

//            toolbarOnlyIcons = "true".equals(properties.getProperty("toolbar.onlyIcons"));
        }
    }

    /**
     * Make the default toolbar from the property resources. It uses the key
     * {@value #DEFAULT_TOOLBAR_PROPERTY}.
     *
     * @return a freshly created toolbar object
     *
     * @throws IOException
     *             on read errors, or configuration error
     */
//    public JToolBar makeToolbar() throws IOException {
//        return makeToolbar(DEFAULT_TOOLBAR_PROPERTY);
//    }

    /**
     * Make a toolbar from the property resources. It uses the key the
     * specified key as starting point
     *
     * @param propertyName
     *            the key in the properties to be used as toolbar definition.
     *
     * @return a freshly created toolbar object
     *
     * @throws IOException
     *             on read errors, or configuration error
     */
    public JToolBar makeToolbar(@NonNull String propertyName) throws IOException {

        prepareProperties();

        JToolBar result = new JToolBar();

        String[] elements = getPropertyOrFail(propertyName).split(" +");

        String val = properties.getProperty(propertyName + ".onlyIcons");
        boolean toolbarOnlyIcons = "true".equals(val);

        for (String element : elements) {
            result.add(makeToolbarItem(element, toolbarOnlyIcons));
        }

        return result;
    }

    /*
     * Make a toolbar item from a given key.
     *
     * SEPARATOR, ACTION, TOGGLE_ACION, TODO, COMMAND
     */
    private JComponent makeToolbarItem(String element, boolean toolbarOnlyIcons)
            throws IOException {

        String value = getPropertyOrFail(element);
        String args[] = value.split(" ", 3);
        JComponent result;
        String val;

        try {
            if(args[0].equals("SEPARATOR")) {
                if(args.length == 3) {
                    int h = Integer.parseInt(args[1]);
                    int w = Integer.parseInt(args[2]);
                    result = new JToolBar.Separator(new Dimension(h, w));
                } else {
                    result = new JToolBar.Separator();
                }

            } else if(args[0].equals("ACTION")) {
                String className = args[1];
                String param = args.length > 2 ? args[2] : null;
                Action action = makeAction(element, param, className);
                JButton button = new JButton(action);

                if(actionListener != null) {
                    button.addActionListener(actionListener);
                }

                if(toolbarOnlyIcons && button.getIcon() != null) {
                    button.setText(null);
                }

                button.setFocusable(false);
                result = button;

            } else if(args[0].equals("TOGGLE_ACTION")) {
                String className = args[1];
                String param = args.length > 2 ? args[2] : null;
                Action action = makeAction(element, param, className);
                JToggleButton button = new JToggleButton(action);

                if(actionListener != null) {
                    button.addActionListener(actionListener);
                }

                if(toolbarOnlyIcons && button.getIcon() != null) {
                    button.setText(null);
                }

                button.setFocusable(false);
                result = button;

            } else if(args[0].equals("COMMAND")) {
                String command = args[1];
                JButton button = new JButton();
                button.setActionCommand(command);

                val =  properties.getProperty(element + ".text");
                if(val != null && !toolbarOnlyIcons) {
                    button.setText(val);
                }

                val = properties.getProperty(element + ".icon");
                if(val != null) {
                    String location = "/" + packagePrefix.replace('.', '/') + val;
                    URL systemResource = BarManager.class.getResource(location);
                    if(systemResource == null) {
                        Log.log(Log.WARNING, "Warning: Unknown icon resource " + location);
                    }
                    button.setIcon(GUIUtil.makeIcon(systemResource));
                    // System.err.println(packagePrefix + "|" +  val + "|" + location);
                }

                val = properties.getProperty(element + ".tooltip");
                if(val != null) {
                    button.setToolTipText(val);
                }

                if(actionListener != null) {
                    button.addActionListener(actionListener);
                }

                button.setFocusable(false);
                result = button;

            } else if(args[0].equals("COMPONENT")) {
                result = makeComponent(element, args[1]);

            } else if(args[0].equals("TODO")){
                JButton button = new JButton(value.substring(5));
                button.setEnabled(false);

                val = properties.getProperty(element + ".icon");
                if(val != null) {
                    String location = "/" + packagePrefix.replace('.', '/') + val;
                    URL systemResource = BarManager.class.getResource(location);
                    if(systemResource == null) {
                        Log.log(Log.WARNING, "Warning: Unknown icon resource " + location);
                    }
                    button.setIcon(GUIUtil.makeIcon(systemResource));
                    // System.err.println(packagePrefix + "|" +  val + "|" + location);
                    if(toolbarOnlyIcons) {
                        button.setText(null);
                    }
                }

                button.setFocusable(false);
                result = button;

            } else {
                throw new IOException("invalid toolbar description: " + element + " = " + value);
            }
        } catch (RuntimeException e) {
            throw new IOException("Illegal format in " + element + " = " + value);
        }

        return result;
    }

    /**
     * Make the default menubar from the property resources. It uses the key
     * {@value #DEFAULT_MENUBAR_PROPERTY}.
     *
     * @return a freshly created menubar object
     *
     * @throws IOException
     *             on read errors, or configuration error
     */
//    public JMenuBar makeMenubar() throws IOException {
//        return makeMenubar(DEFAULT_MENUBAR_PROPERTY);
//    }

    /**
     * Make a menubar from the property resources. It uses the key the specified
     * key as starting point
     *
     * @param propertyName
     *            the key in the properties to be used as menubar definition.
     *
     * @return a freshly created menubar object
     *
     * @throws IOException
     *             on read errors, or configuration error
     */
    public JMenuBar makeMenubar(String propertyName) throws IOException {
        prepareProperties();

        String[] menus = getPropertyOrFail(propertyName).split(" +");

        JMenuBar result = new JMenuBar();

        for (String element : menus) {
            String value = properties.getProperty(element);

            if(value == null) {
                throw new IOException("cannot create menubar, missing property '" + element + "'");
            }

            result.add(makeMenu(element));
        }

        return result;
    }

    /**
     * Make a popup menu from the property resources. It uses the key the
     * specified key as starting point
     *
     * @param propertyName
     *            the key in the properties to be used as menu definition.
     *
     * @return a freshly created popup menu object
     *
     * @throws IOException
     *             on read errors, or configuration error
     */
    public JPopupMenu makePopup(String propertyName) throws IOException {

        prepareProperties();

        String items[] = getPropertyOrFail(propertyName).split(" +");
        JPopupMenu result = new JPopupMenu();

        for (String item : items) {
            result.add(makeMenuItem(item));
        }

        return result;
    }

    /*
     * Make a menu from a given property key.
     */
    private JMenu makeMenu(String property) throws IOException {

        String items[] = getPropertyOrFail(property).split(" +");
        JMenu result = new JMenu(getPropertyOrFail(property + ".text"));

        String mnemonic = properties.getProperty(property + ".mnemonic");
        if(mnemonic != null) {
            result.setMnemonic(mnemonic.charAt(0));
        }

        for (String item : items) {
            // submenu must be ignored - it may appear however as first item.
            // just skip it
            if(item.equals("SUBMENU")) {
                continue;
            }
            result.add(makeMenuItem(item));
        }

        return result;
    }

    /*
     * Make menu item:
     * ACTION, TOGGLE_ACTION, TODO, SUBMENU, RADIO_ACTION, COMMAND, COMPONENT
     */
    private JComponent makeMenuItem(String property) throws IOException {

        JComponent result;

        String value = getPropertyOrFail(property);

        String args[] = value.split(" ", 3);

        try {
            if(args[0].equals("SEPARATOR")) {
                result = new JSeparator();

            } else if(args[0].equals("SUBMENU")) {
                result = makeMenu(property);

            } else if(args[0].equals("ACTION")) {
                String className = args[1];
                String param = args.length > 2 ? args[2] : null;
                Action action = makeAction(property, param, className);
                JMenuItem menuItem = new JMenuItem(action);

                if(actionListener != null) {
                    menuItem.addActionListener(actionListener);
                }

                result = menuItem;

            } else if(args[0].equals("RADIO_ACTION")) {
                String className = args[1];
                String param = args.length > 2 ? args[2] : null;
                Action action = makeAction(property, param, className);
                JRadioButtonMenuItem menuItem = new JRadioButtonMenuItem(action);
                if(actionListener != null) {
                    menuItem.addActionListener(actionListener);
                }

                result = menuItem;

            } else if(args[0].equals("TOGGLE_ACTION")) {
                String className = args[1];
                String param = args.length > 2 ? args[2] : null;
                Action action = makeAction(property, param, className);
                JCheckBoxMenuItem menuItem = new JCheckBoxMenuItem(action);
                if(actionListener != null) {
                    menuItem.addActionListener(actionListener);
                }

                result = menuItem;

            } else if(args[0].equals("COMMAND")) {
                String command = args[1];
                JMenuItem menuItem = new JMenuItem();
                menuItem.setActionCommand(command);

                String val = properties.getProperty(property + ".text");
                if(val != null) {
                    menuItem.setText(val);
                }

                val = properties.getProperty(property + ".icon");
                if(val != null) {
                    String location = packagePrefix.replace('.', '/') + val;
                    menuItem.setIcon(GUIUtil.makeIcon(ClassLoader.getSystemResource(location)));
                }

                val = properties.getProperty(property + ".tooltip");
                if(val != null) {
                    menuItem.setToolTipText(val);
                }

                val = properties.getProperty(property + ".mnemonic");
                if(val != null) {
                    menuItem.setMnemonic(val.charAt(0));
                }

                if(actionListener != null) {
                    menuItem.addActionListener(actionListener);
                }

                result = menuItem;
            } else if(args[0].equals("COMPONENT")) {

                result = makeComponent(property, args[1]);

            } else if(args[0].equals("TODO")){
                JMenuItem menuItem = new JMenuItem(value.substring(5));
                menuItem.setEnabled(false);

                String val = properties.getProperty(property + ".icon");
                if(val != null) {
                    String location = "/" + packagePrefix.replace('.', '/') + val;
                    URL systemResource = BarManager.class.getResource(location);
                    if(systemResource == null) {
                        Log.log(Log.WARNING, "Warning: Unknown icon resource " + location);
                    }
                    menuItem.setIcon(GUIUtil.makeIcon(systemResource));
                }

                val = properties.getProperty(property + ".text");
                if (val != null) {
                    menuItem.setText(val);
                }

                result = menuItem;

            } else {
                throw new IOException("invalid menu description: " + property + " = " + value);
            }
        } catch (RuntimeException e) {
            throw new IOException("Illegal format in " + property + " = " + value, e);
        }

        return result;
    }

    /**
     * Get a property; fail if it is not present.
     * @throws IOException if the property is not set in the resources.
     */
    private String getPropertyOrFail(String property) throws IOException {
        String value = properties.getProperty(property);
        if(value == null) {
            throw new IOException("BarManager: Missing property '" + property +"' in " + resource);
        }
        return value;
    }

    /**
     * Create an action by a property key.
     *
     * @param property
     *            a key to the properties
     *
     * @return the action corresponding to the key.
     *
     * @throws IOException
     *             Signals that an I/O exception has occurred, or that the
     *             property is not set or not an action property.
     */
    public Action makeAction(String property) throws IOException {
        prepareProperties();
        String value = getPropertyOrFail(property);
        String args[] = value.split(" ", 3);

        if(args.length < 2) {
            throw new IOException("The property must at least have two elements: " + property);
        }

        if(!"ACTION".equals(args[0])) {
            throw new IOException("The property must be an ACTION: " + property);
        }

        String param = args.length > 2 ? args[2] : null;

        return makeAction(property, param, args[1]);
    }

    /**
     * Get an action object for a class name.
     *
     * <p>
     * If parameter is <code>null</code>: The object is created, has the
     * properties set and is initialised (if it implements
     * {@link Initialisable}.)
     *
     * <p>
     * If parameter is not <code>null</code>: The object is created and the
     * passed parameter is used as parameter to the constructor. The action has
     * to implement a corresponding constructor!
     *
     * <p>
     * If the method has been called earlier with the same arguments, no new
     * object is created, but the old is returned.
     *
     * @param className
     *            the class name
     *
     * @param parameter
     *            the parameter to give to the action.
     *
     * @return the initialised action
     *
     * @throws IOException
     *             wrapping any exception
     */
    private @NonNull Action makeAction(@NonNull String prefix,
            @Nullable String parameter,
            @NonNull String className) throws IOException {

        if(!className.contains(".")) {
            className = packagePrefix + className;
        }

        // use '/' to escape . to allow for subpackages
        className = className.replace("/", ".");

        try {
            Action cached = actionCache.get(prefix);
            if(cached != null) {
                return cached;
            }

            Class<? extends Action> clss =
                Class.forName(className).asSubclass(Action.class);

            Action action;
            if(parameter == null) {
                action = (Action) clss.newInstance();
            } else {
                Constructor<? extends Action> constr = clss.getConstructor(String.class);
                action = constr.newInstance(parameter);
            }

            initialiseAction(action, prefix);

            actionCache.put(prefix, action);

            return action;
        } catch (Exception e) {
            throw new IOException("cannot create Action instance of " + className, e);
        }
    }

    /**
     * initialise an action. That is: Set all default action properties and, if
     * the action is an instance of {@link Initialisable}, call initialised
     * on it.
     * @param prefix
     */
    private void initialiseAction(Action action, String prefix) {
        for (Entry<String, Object> entry : defaultActionProperties.entrySet()) {
            action.putValue(entry.getKey(), entry.getValue());
        }

        String val = properties.getProperty(prefix + ".text");
        if(val != null) {
            action.putValue(Action.NAME, val);
        }

        val = properties.getProperty(prefix + ".icon");
        if(val != null) {
            String location = "/" + packagePrefix.replace('.', '/') + val;
            action.putValue(Action.SMALL_ICON,
                   GUIUtil.makeIcon(getClass().getResource(location)));
        }

        val = properties.getProperty(prefix + ".tooltip");
        if(val != null) {
            action.putValue(Action.SHORT_DESCRIPTION, val);
        }

        val = properties.getProperty(prefix + ".mnemonic");
        if(val != null) {
            int value = (val.charAt(0) - 'A') + KeyEvent.VK_A;
            action.putValue(Action.MNEMONIC_KEY, value);
        }

        val = properties.getProperty(prefix + ".accelerator");
        if(val != null) {
            KeyStroke keyStroke = KeyStroke.getKeyStroke(val);
            action.putValue(Action.ACCELERATOR_KEY, keyStroke);
        }

        val = properties.getProperty(prefix + ".extra");
        if(val != null) {
            action.putValue(BarAction.EXTRA, val);
        }

        if (action instanceof Initialisable) {
            Initialisable initAction = (Initialisable) action;
            initAction.initialised();
        }
    }

    /**
     * Get a component object for a class name.
     *
     * <p>
     * The object is created and has the properties set as client properties.
     *
     * <p>
     * Every time this method is called, a new component is created.
     *
     * @param property
     *            the name of the property under which the component was invoked
     * @param className
     *            the class name
     *
     * @return the freshly created component
     *
     * @throws IOException
     *             wrapping any exception
     */
    private @NonNull JComponent makeComponent(@NonNull String property, @NonNull String className) throws IOException {
        if(!className.contains(".")) {
            className = packagePrefix + className;
        }

        try {
            Class<?> clss = Class.forName(className);

            JComponent comp = (JComponent) clss.newInstance();

            for (Entry<String, Object> entry : defaultActionProperties.entrySet()) {
                comp.putClientProperty(entry.getKey(), entry.getValue());
            }

            // if there is a key property."params", pass it on to the component
            String paramsKey = property + ".params";
            if(properties.containsKey(paramsKey)) {
                comp.putClientProperty(paramsKey, properties.getProperty(paramsKey));
            }

            // TODO perhaps needed one day: Pass to the component the
            // configuration items of this object (XY=COMPONENT hello,
            // XY.color=green), set property color to green or so

            if (comp instanceof Initialisable) {
                Initialisable init = (Initialisable) comp;
                init.initialised();
            }

            return comp;
        } catch (Exception e) {
            throw new IOException("cannot create JComponent instance of " + className, e);
        }
    }


    /**
     * Clear the cache of actions.
     */
//    @Deprecated
//    public void clearCache() {
//        actionCache.clear();
//    }

    /**
     * Put property into the map of properties to be provided to the actions.
     *
     * <p>
     * <b>Please note:</b> Properties that are set after an action has been
     * created have no effect on already created actions. The will not see the
     * new values.
     *
     * @param property
     *            the property key to set a value for
     * @param value
     *            the value to set for the key.
     */
    public void putProperty(@NonNull String property, Object value) {
        defaultActionProperties.put(property, value);
    }

    public Action getAction(String name) {
        // for (Entry e : actionCache.entrySet())
        // System.out.println(e.getKey() + " -> " + e.getValue());

        return actionCache.get(name);
    }
}
