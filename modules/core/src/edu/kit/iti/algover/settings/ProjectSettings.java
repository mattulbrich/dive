/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.settings;

import edu.kit.iti.algover.project.Configuration;
import edu.kit.iti.algover.term.builder.PVCSequenter;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.StringValidator;
import edu.kit.iti.algover.util.StringValidators;
import edu.kit.iti.algover.util.Util;
import nonnull.NonNull;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * ProjectSettings:
 * * symbex settings: unwind loop, inline methods, use contract
 * * ProverSettings: timeout for z3/dafny/key (DONE), save intermediate po files
 * * ViewSettings: logical view: display ssa; automatically apply simplification, fontsize, tooltipsize
 * * smt settings for cex
 * REVIEW MU:?: has to be called by projectbuilder
 * @author Created by sarah on 8/3/16.
 * @version 2018-Jan. refactored by Mattias
 *
 * @divedoc "Settings"
 *
 * <h2>Project settings</h2>
 *
 * <p>In the header of the main input file, one can set a number of project settings.
 * All of them have default values, i.e., the settings section can be omitted if one is happy with
 * the default values.</p>
 *
 * <p>Settings are embedded into Dafny files as follows, usually at the beginning of the file:</p>
 *
 * <pre>
 * settings {
 *     "Settings key 1" = "Settings Value 1",
 *     "Settings key 2" = "Settings Value 2"
 * }
 * </pre>
 *
 * <p>You can embed this into
 * <a href="dive:/Input Files/Special comments">DIVE special comments</a>.</p>
 *
 * <p>Information about the available settings and valid values for the settings.
 * can be found on subpages.</p>
 *
 */
public class ProjectSettings {

    /**
     * A class that defines a property: name, default value, and checker that
     * can find out if a value is valid or not.
     */
    public static class Property {
        public final String key;
        public final String defaultValue;
        public final StringValidator validator;

        public final String helpText;

        public Property(String key, String defaultValue, StringValidator validator, String helpText) {
            this.key = key;
            this.defaultValue = defaultValue;
            this.validator = validator;
            this.helpText = helpText;
        }
    }

    /* -----------------------------------------------------
     * All available settings should be collected here
     */

    /** @divedoc "Settings/Dafny Timeout"
     *
     * <h2>Project settings: <tt>Dafny Timeout</tt></h2>
     *
     * <p>Set the timeout in seconds which is used for invocations
     * of the Dafny backend via Boogie.</p>
     *
     * <p>Value range: a positive natural number</p>
     * <p>Default value: 5 [seconds]</p>
     */
    public static final Property DAFNY_TIMEOUT_PROP =
            new Property("Dafny Timeout", "5",
                    StringValidators.POSITIVE_VALIDATOR,
                    "Timeout for the Dafny backend solver");

    /** @divedoc "Settings/KeY Timeout"
     *
     * <h2>Project settings: <tt>KeY Timeout</tt></h2>
     *
     * <p>Set the timeout in seconds which is used for invocations
     * of the KeY backend.</p>
     *
     * <p>Value range: a positive natural number</p>
     * <p>Default value: 10 [seconds]</p>
     */
    public static final Property KEY_TIMEOUT_PROP =
            new Property("KeY Timeout", "10",
                    StringValidators.POSITIVE_VALIDATOR,
                    "Timeout for the KeY backend solver");


    /** @divedoc "Settings/SMT Timeout"
     *
     * <h2>Project settings: <tt>SMT Timeout</tt></h2>
     *
     * <p>Set the timeout in seconds which is used for invocations
     * of the SMT backend via Z3.</p>
     *
     * <p>Value range: a positive natural number</p>
     * <p>Default value: 10 [seconds]</p>
     */
    public static final Property SMT_TIMEOUT_PROP =
            new Property("SMT Timeout", "10",
                    StringValidators.POSITIVE_VALIDATOR,
                    "Time out for the selected SMT solver");

    /** @divedoc "Settings/Default Script"
     *
     * <h2>Project settings: <tt>Dafny Timeout</tt></h2>
     *
     * <p>Set the timeout in seconds which is used for invocations
     * of the Dafny backend via Boogie.</p>
     *
     * <p>Value range: a positive natural number</p>
     * <p>Default value: 5 [seconds]</p>
     */
    public static final Property DEFAULT_SCRIPT_PROP =
            new Property("Default Script", "",
                    StringValidators.ANY_VALIDATOR,
                    "The commands that should be executed as default script ");

    /** @divedoc "Settings/Sequent Generation Type"
     *
     * <h2>Project settings: <tt>Sequent Generation Type</tt></h2>
     *
     * <p>Set the sequent style that should be used for verification condition generation.
     * They are explained under <a href="dive:/VC generation">Verification Condition Generation</a>.</p>
     *
     * <p>Value range: One of the values summarised here <a href="VC generation">here</a>.</p>
     * <p>Default value: "ass-simp"</p>
     */
    public static final Property SEQUENTER_PROP = new Property("Sequent Generation Type",
            PVCSequenter.INSTANCES.get(0).getName(),
            StringValidators.oneOfValidator(Util.map(PVCSequenter.INSTANCES, PVCSequenter::getName)),
            createHelpTextForSequenter(PVCSequenter.INSTANCES));

    private static final Property[] DEFINED_PROPERTIES = {
            DAFNY_TIMEOUT_PROP,
            KEY_TIMEOUT_PROP,
            SMT_TIMEOUT_PROP,
            SEQUENTER_PROP,
            DEFAULT_SCRIPT_PROP,
    };


    /**
     * data structure holding values of the settings
     */
    private Map<String, String> set;

    public ProjectSettings() {
        set = new HashMap<>();
        setDefaultValues();
    }

    public ProjectSettings(@NonNull Map<String, String> settings) {
        this();
        set.putAll(settings);
    }

    /**
     * Set default values for all settings
     */
    private void setDefaultValues() {
        for (Property property : DEFINED_PROPERTIES) {
            set.put(property.key, property.defaultValue);
        }
    }

    public void validate() throws FormatException {
        Set<String> usedKeys = new HashSet<>(set.keySet());
        for (Property property : DEFINED_PROPERTIES) {
            String str = set.get(property.key);
            assert str != null : "Caution, default value not set ?!";
            property.validator.validate(str);
            usedKeys.remove(property.key);
        }

        if(!usedKeys.isEmpty()) {
            throw new FormatException("settings", "Unsupported setting key(s)", usedKeys.toString());
        }

    }

    public String getString(String key) {
        return set.get(key);
    }

    public int getInt(String key) {
        return Integer.parseInt(set.get(key));
    }

    public boolean getBoolean(String key) {
        return Boolean.valueOf(set.get(key));
    }

    public static List<Property> getDefinedProperties() {
        return Util.readOnlyArrayList(DEFINED_PROPERTIES);
    }

    public static Map<String, Property> getDefinedPropertyMap() {
        Map<String, Property> result = new HashMap<>();
        for (Property definedProperty : getDefinedProperties()) {
            result.put(definedProperty.key, definedProperty);
        }
        return result;
    }


    public String toString() {
        return set.toString();
    }



    /**
     * Returns a Configuration object holding only the settings
     * @return
     */
    public Configuration getConfiguration(){
        Configuration c = new Configuration();
        c.setSettings(this.set);
        return c;
    }

    private static String createHelpTextForSequenter(List<PVCSequenter> instances) {
        StringBuilder s = new StringBuilder();
        s.append("The way in which assignments should be transformed during translation.<br> The following options exists:");
        s.append("<br><br>");
        s.append("<ul>");
        for (PVCSequenter instance : instances) {
            s.append("<li>");
            s.append(instance.getName()+": "+instance.getDescriptiveName()+"\n");
            s.append("</li>");
        }
        s.append("</ul>");
        return s.toString();
    }

}



