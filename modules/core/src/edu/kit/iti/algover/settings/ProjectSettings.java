package edu.kit.iti.algover.settings;

import edu.kit.iti.algover.term.builder.PVCSequenter;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.StringValidator;
import edu.kit.iti.algover.util.StringValidators;
import edu.kit.iti.algover.util.Util;
import nonnull.NonNull;

import javax.xml.bind.annotation.XmlType;
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
 */
public class ProjectSettings {

    public static class Property {
        public final String key;
        public final String defaultValue;
        public final StringValidator validator;

        public Property(String key, String defaultValue, StringValidator validator) {
            this.key = key;
            this.defaultValue = defaultValue;
            this.validator = validator;
        }
    }

    /**
     * Available settings should be collected here, including their default values.
     */

    public static final String DAFNY_TIMEOUT = "Dafny Timeout";
    public static final String KEY_TIMEOUT = "KeY Timeout";
    public static final String SMT_TIMEOUT = "SMT Timeout";
    public static final String SYMBEX_UNROLL_LOOPS = "Unroll Loops";
    public static final String SYMBEX_INLINE_METHODS = "Inline Methods";
    public static final String SEQUENTER = "Sequent Generation Type";
    public static final String DEFAULT_SCRIPT = "Default Script";

    private static final Property DEFINED_PROPERTIES[] = {
            new Property(DAFNY_TIMEOUT, "5", StringValidators.POSITIVE_VALIDATOR),
            new Property(KEY_TIMEOUT, "10", StringValidators.POSITIVE_VALIDATOR),
            new Property(SMT_TIMEOUT, "10", StringValidators.POSITIVE_VALIDATOR),
            new Property(SYMBEX_UNROLL_LOOPS, "false", StringValidators.BOOLEAN_VALIDATOR),
            new Property(SYMBEX_INLINE_METHODS, "false", StringValidators.BOOLEAN_VALIDATOR),
            new Property(SEQUENTER,
                    PVCSequenter.INSTANCES.get(0).getName(),
                    StringValidators.oneOfValidator(Util.map(PVCSequenter.INSTANCES, PVCSequenter::getName))),
            new Property(DEFAULT_SCRIPT, "", StringValidators.ANY_VALIDATOR),
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

    public String toString() {
        return set.toString();
    }
}



