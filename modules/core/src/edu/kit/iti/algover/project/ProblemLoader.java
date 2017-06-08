package edu.kit.iti.algover.project;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;
import java.io.File;

/**
 * Handles loading XML-Config Files
 *
 * @author S.Grebing
 */
public class ProblemLoader {


    public ProblemLoader() {

    }

    /**
     * Read teh XML Config File and parse it into a Configuration object
     *
     * @param configFile
     * @return Configuration object holding all fields of the XML file
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
