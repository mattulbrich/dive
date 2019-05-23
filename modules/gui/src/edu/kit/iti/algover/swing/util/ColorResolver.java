
package edu.kit.iti.algover.swing.util;

import java.awt.Color;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.HashMap;
import java.util.Map;

import javax.swing.UIManager;

import nonnull.NonNull;
import nonnull.Nullable;

/**
 * A class with a singleton object to be used to resolve color names to Color objects.
 * 
 * <p>It allows to convert strings to {@link Color} objects.
 * Colors can either be specified as hexadecimal (or decimal) constants, as names or
 * as references to colors defined by the UI. 
 * 
 * <p>The color names are read from a <code>colors.properties</code> resource in 
 * this directory. Color objects that have been queried once are cached, so that no
 * unnecessary memory is spent on color objects. 
 * 
 * TODO Use weak references (though WeakHashMap is not adequate). 
 * 
 * @author mattze
 */

public class ColorResolver {

    private static final String UI_REFERENCE_PREFIX = "UI:";

    private static ColorResolver defaultInstance;

    private Map<String, Integer> lookuptable;
    private Map<Integer, Color> cache;

    private ColorResolver() throws IOException {
        lookuptable = new HashMap<String, Integer>();
        cache = new HashMap<Integer, Color>();
        load(getClass().getResourceAsStream("colors.properties"));
    }

    /**
     * Get the instance of the ColorResolver.
     * 
     * Try tp create if not yet created.
     * 
     * @return the color resolver, null if resource is unavailable.
     */
    public static @NonNull ColorResolver getInstance() {
        if (defaultInstance == null) {
            try {
                defaultInstance = new ColorResolver();
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
        return defaultInstance;
    }

    /**
     * resolve a String to a color.
     * 
     * Valid color names are either the ones stored in "colors.properties", or an
     * integer constant in either decimal or hexadecimal format, or a reference to
     * a UI color prefixed with <code>{@value #UI_REFERENCE_PREFIX}</code>.
     * 
     * Results are stored in a cache table.
     * 
     * @param colorString
     *            a name of a color or a string containing an integer or
     *            a reference to a UI reference.
     * @return a Color object, possibly cached, null if the named color has not
     *         been found
     */
    public @Nullable Color resolve(@NonNull String colorString) {
        try {
            
            if(colorString.startsWith(UI_REFERENCE_PREFIX)) {
                Color color = UIManager.getColor(colorString.substring(UI_REFERENCE_PREFIX.length()));
                if(color != null)
                    return color;
            }
            
            Integer entry = lookuptable.get(colorString);
            
            if (entry == null) {
                try {
                    entry = Integer.decode(colorString);
                } catch (NumberFormatException ex) {
                    // no valid number --> return null
                }
            }
            
            if(entry == null)
                return null;

            Color c = cache.get(entry);
            if(c == null) {
                c = new Color(entry);
                cache.put(entry, c);
            }
            
            return c;

        } catch (Exception ex) {
            throw new RuntimeException("colors.properties has bad format!", ex);
        }
    }

    private void load(InputStream is) throws IOException {
        BufferedReader br = new BufferedReader(new InputStreamReader(is));

        String line = br.readLine();
        while (line != null) {
            line = line.trim();
            if (line.length() == 0 || line.charAt(0) == '#') {
                line = br.readLine();
                continue;
            }

            String[] parts = line.split(" += +");
            int intVal = Integer.decode(parts[1]);
            lookuptable.put(parts[0], intVal);
            line = br.readLine();
        }
    }
}
