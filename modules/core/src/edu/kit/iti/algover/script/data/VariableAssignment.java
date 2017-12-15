package edu.kit.iti.algover.script.data;

import edu.kit.iti.algover.script.ast.Type;
import edu.kit.iti.algover.script.ast.Variable;
import edu.kit.iti.algover.script.exceptions.VariableNotDefinedException;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Variable Assignments for each goal node
 *
 * @author S.Grebing
 */
public class VariableAssignment {
    private final VariableAssignment parent;
    private Map<Variable, Value> values = new HashMap<>();
    private Map<Variable, Type> types = new HashMap<>();

    public VariableAssignment(VariableAssignment parent) {
        this.parent = parent;
    }

    public VariableAssignment() {
        this(null);
    }

    /**
     * returns the parent assignment or null
     *
     * @return
     */
    public VariableAssignment getParent() {
        return parent;
    }

    /**
     * returns the map of values in this assignment
     *
     * @return
     */
    public Map<Variable, Value> getValues() {
        return values;
    }

    /**
     * * returns the map of types of this assignment
     *
     * @return
     */
    public Map<Variable, Type> getTypes() {
        return types;
    }

    public Type getType(Variable name) {
        if (parent == null) {
            return types.getOrDefault(name, null);
        } else {
            return types.getOrDefault(name, parent.getType(name));
        }
    }


    /**
     * Lookup value of variable also in parent assignments
     *
     * @param name
     * @return
     */
    public Value getValue(Variable name) {
        if (values.containsKey(name))
            return values.get(name);
        else {
            if (parent != null) {
                return parent.getValue(name);
            } else {
                throw new VariableNotDefinedException();
            }
        }
    }

    /**
     * @param name
     * @param type
     * @return
     * @throws NullPointerException
     * @throws RuntimeException
     */
    public VariableAssignment declare(Variable name, Type type) {
        if (name == null || type == null)
            throw new NullPointerException("name or type are not allowed to be null");

        if (getType(name) == null) {
            this.types.put(name, type);
            return this;
        } else {
            throw new RuntimeException("Variable " + name + " is already declared with type " + type.toString());
        }
    }

    public VariableAssignment declare(String name, Type type) {
        return declare(new Variable(name), type);
    }


    /**
     * enterscope
     *
     * @return
     */
    public VariableAssignment push() {
        return new VariableAssignment(this);
    }

    /**
     * leavescope
     *
     * @return
     */
    public VariableAssignment pop() {
        return getParent();
    }

    /**
     * @param name
     * @param value
     * @return
     */
    public VariableAssignment assign(Variable name, Value value) {
        VariableAssignment temp = this;
        if (this.getTypes().containsKey(name)) {
            this.values.put(name, value);
        } else {
            if (parent != null) {
                parent.assign(name, value);
            } else {
                throw new RuntimeException("Variable " + name + " needs to be declared first");
            }
        }
        return temp;
    }

    public VariableAssignment assign(String name, Value value) {
        return assign(new Variable(name), value);
    }

    /**
     * except parent
     *
     * @return
     */
    public VariableAssignment deepCopy() {
        VariableAssignment va = new VariableAssignment(parent);
        types.forEach((k, v) -> va.types.put(k, v));
        values.forEach((k, v) -> va.values.put(k, v));
        return va;
    }

    private Map<Variable, Value> asMap(Map<Variable, Value> map) {
        if (parent != null) {
            parent.asMap(map);
        }
        map.putAll(this.values);
        return map;
    }

    /**
     * @return
     */
    public Map<Variable, Value> asMap() {
        return asMap(new HashMap<>());
    }

    /**
     * Method joins two variable assignments without checking their compatibility
     *
     * @param assignment
     * @return a new Variable Assignment
     */
    public VariableAssignment joinWithoutCheck(VariableAssignment assignment) {
        VariableAssignment va = new VariableAssignment(null);
        va.getValues().putAll(assignment.getValues());
        va.getTypes().putAll(assignment.getTypes());
        return va;
    }

    /**
     * @param assignment
     * @return empty variable assignment if not possible to join conflictfree (i.e., if a variable name is present
     * in both assignments with different types or dfferent values) the join otherwise
     * @throws RuntimeException
     */
    public VariableAssignment joinWithCheck(VariableAssignment assignment) {

        Set<Variable> namesV2 = assignment.getValues().keySet();
        //create intersection
        Set<Variable> conflictingCand = this.getValues()
                .keySet().stream()
                .filter(namesV2::contains)
                .collect(Collectors.toSet());

        if (!conflictingCand.isEmpty()) {
            for (Variable s : conflictingCand) {
                if (!this.getValue(s).equals(assignment.getValue(s))) {
                    return new VariableAssignment(null);
                }
            }
        }

        return this.joinWithoutCheck(assignment);
    }

    /**
     * checks whether an assignment is empty i.e. does not contain type declarations and values
     *
     * @return
     */
    public boolean isEmpty() {
        if (this.getValues().isEmpty() && this.parent != null) {
            return this.getParent().isEmpty();
        } else {
            return this.getValues().isEmpty();
        }
    }

    /**
     * @param va
     * @return
     */
    public VariableAssignment push(VariableAssignment va) {
        VariableAssignment nva = push();
        nva.types.putAll(va.types);
        nva.values.putAll(va.values);

        return nva;
    }

    public String toString() {
        return "Var-Assignments: (\nparent=" + this.getParent()
                + ",\n values=" + this.getValues() + ",\n types=" + this.getTypes() + ")";
    }
}
