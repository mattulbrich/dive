/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.util;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

public class LineProperties {

    private Map<String, String> map = new LinkedHashMap<>();

    public void read(InputStream is) throws IOException {
        read(new InputStreamReader(is));
    }

    private void read(Reader reader) throws IOException {
        BufferedReader br = new BufferedReader(reader);

        String line;
        StringBuffer sb = new StringBuffer();
        String lastKey = null;

        while ((line = br.readLine()) != null) {
            if (line.startsWith("###")) {
                if(lastKey != null) {
                    String str = sb.toString().trim();
                    if (str.length() > 0) {
                        map.put(lastKey, str);
                    }
                }
                sb.setLength(0);

                lastKey = line.substring(3).trim();
                if(lastKey.endsWith(":")) {
                    lastKey = lastKey.substring(0, lastKey.length() - 1);
                }
            } else {
                sb.append(line).append("\n");
            }
        }

        if(lastKey != null) {
            String str = sb.toString().trim();
            if (str.length() > 0) {
                map.put(lastKey, str);
            }
        }

    }

    public String get(Object key) {
        return map.get(key);
    }

    public Set<String> keySet() {
        return map.keySet();
    }

    public Set<Entry<String, String>> entrySet() {
        return map.entrySet();
    }

    public String getOrDefault(Object key, String defaultValue) {
        return map.getOrDefault(key, defaultValue);
    }

    public List<String> getLines(String key) {
        String str = get(key);
        if (str == null) {
            return Collections.emptyList();
        }
        return Arrays.asList(str.split("\n"));
    }
}
