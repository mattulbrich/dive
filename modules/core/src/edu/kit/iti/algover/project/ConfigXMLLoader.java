/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import org.xml.sax.SAXException;

import javax.xml.XMLConstants;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.StringWriter;

/**
 * Handles loading XML config files.
 *
 * @author S.Grebing
 */

public class ConfigXMLLoader {


    private ConfigXMLLoader() {
        throw new Error();
    }

    /**
     * Read the XML config file and parse it into a {@link Configuration} object
     *
     * @param configFile
     *            non-<code>null</code> file object of the xml file.
     * @return {@link Configuration} object holding all fields of the XML file
     */
    public static Configuration loadConfigFile(File configFile) throws JAXBException, SAXException {

        SchemaFactory sf = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
        assert ConfigXMLLoader.class.getResourceAsStream("config-schema.xsd") != null;
        Schema schema = sf.newSchema(ConfigXMLLoader.class.getResource("config-schema.xsd"));

        JAXBContext jaxbContext = JAXBContext.newInstance(Configuration.class);

        Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
        jaxbUnmarshaller.setSchema(schema);
        Configuration config = (Configuration) jaxbUnmarshaller.unmarshal(configFile);

        return config;
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
            // REVIEW: This is not a good exception handling concept. Why throw the exception away?
            e.printStackTrace();
        }
    }

    /**
     * Return a configuration object as XML string
     *
     * @param config   object holdingall project settings
     */
    public static String toString(Configuration config) throws JAXBException {

        JAXBContext jaxbContext = JAXBContext.newInstance(Configuration.class);
        Marshaller jaxbMarshaller = jaxbContext.createMarshaller();

        // output pretty printed
        jaxbMarshaller.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, true);

        StringWriter w = new StringWriter();
        jaxbMarshaller.marshal(config, w);
        return w.toString();
    }
}
