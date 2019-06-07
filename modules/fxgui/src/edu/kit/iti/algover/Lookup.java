package edu.kit.iti.algover;

import java.util.*;

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
     * Register
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

    public <T> void deregister(T obj, Class<T> service) {
        boolean b = getList(service).remove(obj);
    }

    @SuppressWarnings("unchecked")
    private <T> List<T> getList(Class<T> service) {
        return (List<T>) serviceMap.computeIfAbsent(service, (k -> new LinkedList<>()));
    }
}
