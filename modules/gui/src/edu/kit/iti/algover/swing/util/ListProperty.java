package edu.kit.iti.algover.swing.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

@SuppressWarnings({"unchecked", "raw"})
public class ListProperty<T> extends Property<List<T>> {

    private final Class<T> elementType;

    public ListProperty(String name, Class<T> elementType) {
        super(name, (Class)List.class, new ArrayList<T>());
        this.elementType = elementType;
    }

    public ListProperty(String name, Class<T> elementType, Collection<? extends T> value) {
        this(name, elementType);
        setValue(value);
    }

    public void setValue(Collection<? extends T> value) {
        setValue(null, value);
    }


    public void setValue(Object origin, Collection<? extends T> value) {
        List<T> list = super.getValue();

        if(!(value instanceof List)) {
            value = new ArrayList<T>(value);
        }

        boolean changed = !list.equals(value);

        list.clear();
        list.addAll(value);

        if(changed) {
            notifyObservers();
        }
    }

    @Override
    public List<T> getValue() {
        return Collections.unmodifiableList(super.getValue());
    }

    public void setElement(int index, T value) {
        List<T> list = super.getValue();

        T old = list.get(index);
        list.set(index, value);

        if(!old.equals(value)) {
            notifyObservers();
        }
    }

    public void addElement(T value) {
        List<T> list = super.getValue();
        list.add(value);
        notifyObservers();
    }

    public void removeElement(int index) {
        List<T> list = super.getValue();
        list.remove(index);
        notifyObservers();
    }

    @Override
    public String exportString() {
        if(getValue().isEmpty()) {
            return "#empty";
        }

        StringBuilder sb = new StringBuilder();
        for (T t : getValue()) {
            if(sb.length() > 0) {
                sb.append(", ");
            }
            sb.append(t.toString().replace("\\", "\\\\").replace(",", "\\,"));
        }
        return sb.toString();
    }

}
