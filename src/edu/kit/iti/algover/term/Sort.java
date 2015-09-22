package edu.kit.iti.algover.term;

public class Sort {

    public static final Sort FORMULA = new Sort("formula");
    public static final Sort INT = new Sort("int");
    public static final Sort INT_SET = new Sort("set");

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

    public String getName() {
        return name;
    }

}
