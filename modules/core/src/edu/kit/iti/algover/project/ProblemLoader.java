/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;
import java.io.File;

/**
 * Handles loading XML config files.
 *
 * @author S.Grebing
 */
// REVIEW: Is ProblemLoader a good name?
public class ProblemLoader {

    // REVIEW: I assumed this class is a collection of static methods, right?
    private ProblemLoader() {
        throw new Error();
    }

    /**
     * Read the XML config file and parse it into a {@link Configuration} object
     *
     * @param configFile
     *            non-<code>null</code> file object of the xml file.
     * @return {@link Configuration} object holding all fields of the XML file
     */
    public static Configuration loadConfigFile(File configFile) {

        try {

            JAXBContext jaxbContext = JAXBContext.newInstance(Configuration.class);

            Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
            Configuration config = (Configuration) jaxbUnmarshaller.unmarshal(configFile);

            return config;

        } catch (JAXBException e) {
            e.printStackTrace();
        }
        return null;

    }

    /**
     * Save a configuration object as XML to a file
     *
     * @param config   object holdingall project settings
     * @param filename file to save to
     */
    public static void saveConfigFile(Configuration config, File filename) {
        try {

            JAXBContext jaxbContext = JAXBContext.newInstance(Configuration.class);
            Marshaller jaxbMarshaller = jaxbContext.createMarshaller();

            // output pretty printed
            jaxbMarshaller.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, true);

            jaxbMarshaller.marshal(config, filename);
            jaxbMarshaller.marshal(config, System.out);

        } catch (JAXBException e) {
            e.printStackTrace();
        }
    }
}
