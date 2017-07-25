/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.prettyprint;

import java.io.IOException;
import java.io.InputStream;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.Unmarshaller;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElements;
import javax.xml.bind.annotation.XmlRootElement;

@XmlRootElement(name = "operators")
class FixOperatorCollection {

    private static Map<String, FixOperatorInfo> MAP;

    @XmlElements(@XmlElement(name="operator"))
    List<FixOperatorInfo> operators;


    static class FixOperatorInfo {

        @XmlElement
        private String name;

        @XmlElement
        private String op;

        @XmlElement
        private int precedence;

        public int getPrecedence() {
            return precedence;
        }

        public String getOp() {
            return op;
        }

        public String getName() {
            return name;
        }

        @Override
        public String toString() {
            return "FixOperatorInfo [name=" + name + ", op=" + op + ", precedence=" + precedence + "]";
        }

    }
    public static FixOperatorInfo get(String fctname) {
        ensureMapExists();
        return MAP.get(fctname);
    }

    private static void ensureMapExists() {
        if(MAP == null) {
            try(InputStream is = FixOperatorCollection.class.getResourceAsStream("operators.xml")) {
                if (is == null) {
                    throw new IOException("unknown resource");
                }

                JAXBContext jaxbContext = JAXBContext.newInstance(FixOperatorCollection.class);

                Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
                FixOperatorCollection coll = (FixOperatorCollection) jaxbUnmarshaller.unmarshal(is);

                Map<String, FixOperatorInfo> map = new HashMap<>();
                for (FixOperatorInfo info : coll.operators) {
                    map.put(info.name, info);
                }

                MAP = map;
            } catch (Exception e) {
                e.printStackTrace();
                MAP = Collections.emptyMap();
            }

        }
    }
}