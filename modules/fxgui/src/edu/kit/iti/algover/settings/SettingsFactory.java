package edu.kit.iti.algover.settings;

import edu.kit.iti.algover.project.Configuration;
import static java.util.ServiceLoader.load;

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
     * Gather the list of all current settings panel.
     * @return non-null list of Node
     */
    public static List<ISettingsController> getSettingsPanel(SettingsWrapper settings){
        return supplier.stream().map(i -> i.apply(settings)).collect(Collectors.toList());
    }

    public static List<ISettingsController> getSettingsPanel() {
        return getSettingsPanel(new SettingsWrapper());
    }
}
