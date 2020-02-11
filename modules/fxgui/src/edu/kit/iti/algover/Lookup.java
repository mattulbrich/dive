package edu.kit.iti.algover;

import java.util.*;

/**
 * Lookup object as also implemented in the KeY system to be able to register
 * handlers (classes implementing specific interfacers) for different services in the GUI.
 * Controllers can register here if they offer services that are announced by interfaces
 * One example is the
 * {@link edu.kit.iti.algover.referenceHighlighting.ReferenceHighlightingHandler} to
 * highlight references in the different GUI elements
 */
public class Lookup {

    /**
     * Registered services. The first service in the list is the default.
     */
    private final HashMap<Class<?>, LinkedList<?>> serviceMap = new HashMap<>();

    public Lookup(){

    }


    /**
     * Get all registered implementations for the given service class.
     *
     * @param service
     * @param <T>
     * @return
     */
    public <T> Collection<T> lookupAll(Class<T> service) {
        ArrayList<T> t = new ArrayList<>(getList(service));
        return t;

    }

    /**
     * Register an object implementing a service
     *
     * @param obj
     * @param service
     * @param <T>
     */
    @SuppressWarnings("unchecked")
    public <T> void register(T obj, Class<T> service) {
        List<T> list = getList(service);
        list.add(0, obj);
    }

    /**
     * Deregister an object if the service should not be available anymore
     * @param obj
     * @param service
     * @param <T>
     */
    public <T> void deregister(T obj, Class<T> service) {
        boolean b = getList(service).remove(obj);
    }

    @SuppressWarnings("unchecked")
    private <T> List<T> getList(Class<T> service) {
        return (List<T>) serviceMap.computeIfAbsent(service, (k -> new LinkedList<>()));
    }
}
