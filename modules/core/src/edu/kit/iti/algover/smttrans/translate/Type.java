package edu.kit.iti.algover.smttrans.translate;

import java.util.Arrays;
import java.util.List;

import com.google.common.base.CharMatcher;
import com.google.common.base.Splitter;
import com.google.common.collect.Iterables;
import com.google.common.primitives.Ints;

public class Type {

    List<String> typeData;

    public Type(List<String> types) {
        // this.typeData = inferType(types); // TODO
        this.typeData = types;

    }

    public static Type typeOperation(String poly) {

        String typedOp = CharMatcher.anyOf(">").removeFrom(poly);
        Iterable<String> operators = Splitter.on("<").split(typedOp);
        List<String> ops = Arrays.asList(Iterables.toArray(operators, String.class));
        return new Type(ops);

    }

    private List<String> inferType(List<String> data) { // TODO
        List<String> type;
        if (data.get(0).startsWith("$")) {
            type = data.subList(1, data.size());
        } else {
            type = data;
        }
        // if (type.size() == 1) { //TODO necessary ?
        // String t = (Ints.tryParse(type.get(0)) == null) ? "Bool" : "Int"; // TODO
        // Sorts
        //
        // }
        return type;
    }

    @Override
    public String toString() {
        String ty = "";
        for (String s : this.typeData) {
            ty += s.substring(0, 1).toUpperCase() + s.substring(1);
        }
        return ty;
    }
}
