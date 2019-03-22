package edu.kit.iti.algover.settings;

import edu.kit.iti.algover.term.builder.SSASequenter;
import static java.util.ServiceLoader.load;
import javafx.scene.Node;

import java.util.ArrayList;
import java.util.List;
import java.util.ServiceLoader;
import java.util.stream.Collectors;

public class SettingsFactory {
    private static List<SettingsSupplier> supplier = new ArrayList<>();

    static {
        ServiceLoader<SettingsSupplier> serviceLoader = load(SettingsSupplier.class);
        serviceLoader.forEach(a -> supplier.add(a));
    }

//TODO error handling

    public static void register(SettingsSupplier ss){
        supplier.add(ss);
    }

    public static void deregister(SettingsSupplier ss){
        supplier.remove(ss);
    }


    /**
     * Gather the list of all current settigns panel.
     * @return non-null list of Node
     */
    public static List<Node> getSettingsPanel(){
        return supplier.stream().map(i -> i.getNode()).collect(Collectors.toList());
    }


    /**
     * Send the event, that the setting dialog was closed, to all of the known settings panel.
     */
    public static void fireOnSave(){
        supplier.stream().forEach(i -> i.save());
    }

}
