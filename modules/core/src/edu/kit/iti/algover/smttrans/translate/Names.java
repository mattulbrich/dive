package edu.kit.iti.algover.smttrans.translate;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;

public class Names {
    // AV <-> SMT
    //private static BiMap<String, String> names = HashBiMap.create();
  private static BiMap<String, String> names = TypeContext.getDefaults();
    private static String PREFIX = "~";

    public static String makeSMTName(String avName) {
        String smtName = PREFIX + avName;
        names.put(avName, smtName);
        return smtName;
    }

    public static String toSMT(String key) {
        return names.getOrDefault(key,key);

    }

    public static String toAV(String key) {
        return names.inverse().getOrDefault(key,key);

    }

}
