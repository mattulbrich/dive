package edu.kit.iti.algover.term;

public class Sort {

    public static final Sort FORMULA = new Sort("Formula");

    private final String name;

    public Sort(String name) {
        this.name = name;
    }

    @Override
    public int hashCode() {
        return name.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof Sort) {
            Sort sort = (Sort) obj;
            return name.equals(sort.name);
        }
        return false;
    }

}
