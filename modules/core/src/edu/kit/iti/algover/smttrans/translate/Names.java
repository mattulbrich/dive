package edu.kit.iti.algover.smttrans.translate;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;

public class Names {
    // AV <-> SMT
  //private static BiMap<String, String> names = TypeContext.getDefaults();
  private static BiMap<String, String> names = HashBiMap.create();
    
    private static String PREFIX = "~";
    
    public static String getPrefix() {
        return PREFIX;
    }
    
    public static BiMap<String, String> getNames() {
        return names;
    }

    public static String makeSMTName(String avName) {
        String smtName = PREFIX + avName;
        names.put(avName, smtName);
        return smtName;
    }

    public static String toSMT(String key) {
        if (key.startsWith("$")) {
            return names.getOrDefault(key.substring(1),key.substring(1));
        }
        return names.getOrDefault(key,key);

    }

    public static String toAV(String key) {
        return names.inverse().getOrDefault(key,key);

    }

}
