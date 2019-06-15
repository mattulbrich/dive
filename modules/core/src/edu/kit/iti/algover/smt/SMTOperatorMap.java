/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.smt;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.Unmarshaller;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElements;
import javax.xml.bind.annotation.XmlRootElement;

import edu.kit.iti.algover.smt.SExpr.Type;
import edu.kit.iti.algover.smt.SMTOperatorMap.OperatorEntry;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.FunctionSymbolFamily.InstantiatedFunctionSymbol;

@XmlRootElement(name = "SMT_operators")
public class SMTOperatorMap {

    private Map<String, OperatorEntry> map;
    @XmlElements(@XmlElement(name = "operator"))
    private List<OperatorEntry> list;

    public static SMTOperatorMap deserialize(URL url) throws IOException {
        try (InputStream is = url.openStream()) {
            JAXBContext jaxbContext =
                    JAXBContext.newInstance(SMTOperatorMap.class);

            Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
            SMTOperatorMap coll = (SMTOperatorMap) jaxbUnmarshaller.unmarshal(is);
            return coll;
        } catch (IOException ex) {
            throw ex;
        } catch (Exception ex) {
            throw new IOException(ex);
        }
    }

    public boolean contains(String function) {
        return lookup(function) != null;
    }

    public OperatorEntry lookup(String operator) {
        if (map == null) {
            Map<String, OperatorEntry> newMap = new HashMap<>();
            for (OperatorEntry entry : list) {
                newMap.put(entry.function, entry);
            }
            map = newMap;
        }
        return map.get(operator);
    }

    public OperatorEntry lookup(FunctionSymbol f) {
        OperatorEntry entry = lookup(f.getName());
        if (entry == null && f instanceof InstantiatedFunctionSymbol) {
            InstantiatedFunctionSymbol ifs = (InstantiatedFunctionSymbol) f;
            String basename = ifs.getFamily().getBaseName();
            entry = lookup(basename);
        }

        return entry;
    }

    public interface SMTExporter {
        SExpr translate(OperatorEntry entry, SMTTrans trans, ApplTerm term) throws SMTException;
    }

    public static class OperatorEntry {
        @XmlElement
        private String function;
        @XmlElement
        private String smtFunction;
        @XmlElements(@XmlElement(name = "argument"))
        private Type arguments[];
        @XmlElement
        private Type result;
        @XmlElement
        private String exporterClass;
        private SMTExporter exporter;

        public String getFunction() {
            return function;
        }

        public String getSmtFunction() {
            return smtFunction;
        }

        public Type[] getArguments() {
            return arguments;
        }

        public Type getResult() {
            return result;
        }

        public SMTExporter getExporter() throws SMTException {
            if (exporter == null) {
                String name = exporterClass;
                if (name == null) {
                    name = "BuiltinSymbolSMTExporter";
                }
                name = "edu.kit.iti.algover.smt." + name;

                try {
                    exporter = (SMTExporter) Class.forName(name).newInstance();
                } catch (Exception e) {
                    throw new SMTException(e);
                }
            }
            return exporter;
        }
    }
}
