package edu.kit.iti.algover.script.ast;

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */


import edu.kit.iti.algover.script.ScriptLanguageParser;
import edu.kit.iti.algover.script.parser.Visitor;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;

/**
 * @author Alexander Weigl
 * @version 1 (29.04.17)
 */
public class Parameters extends ASTNode<ScriptLanguageParser.ParametersContext> {
    private final Map<Variable, Expression> parameters = new LinkedHashMap<>();

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public Parameters copy() {
        Parameters p = new Parameters();
        forEach((k, v) -> p.put(k.copy(), v.copy()));
        return p;
    }

    public int size() {
        return parameters.size();
    }

    public boolean isEmpty() {
        return parameters.isEmpty();
    }

    public boolean containsKey(Object key) {
        return parameters.containsKey(key);
    }

    public boolean containsValue(Object value) {
        return parameters.containsValue(value);
    }

    public Expression get(Object key) {
        return parameters.get(key);
    }

    public Expression put(Variable key, Expression value) {
        return parameters.put(key, value);
    }

    public Expression remove(Object key) {
        return parameters.remove(key);
    }

    public void putAll(Map<? extends Variable, ? extends Expression> m) {
        parameters.putAll(m);
    }

    public void clear() {
        parameters.clear();
    }

    public Set<Variable> keySet() {
        return parameters.keySet();
    }

    public Collection<Expression> values() {
        return parameters.values();
    }

    public Set<Map.Entry<Variable, Expression>> entrySet() {
        return parameters.entrySet();
    }

    public Expression getOrDefault(Object key, Expression defaultValue) {
        return parameters.getOrDefault(key, defaultValue);
    }

    public void forEach(BiConsumer<? super Variable, ? super Expression> action) {
        parameters.forEach(action);
    }

    public void replaceAll(BiFunction<? super Variable, ? super Expression, ? extends Expression> function) {
        parameters.replaceAll(function);
    }

    public Expression putIfAbsent(Variable key, Expression value) {
        return parameters.putIfAbsent(key, value);
    }

    public boolean remove(Object key, Object value) {
        return parameters.remove(key, value);
    }

    public boolean replace(Variable key, Expression oldValue, Expression newValue) {
        return parameters.replace(key, oldValue, newValue);
    }

    public Expression replace(Variable key, Expression value) {
        return parameters.replace(key, value);
    }

    public Expression computeIfAbsent(Variable key, Function<? super Variable, ? extends Expression> mappingFunction) {
        return parameters.computeIfAbsent(key, mappingFunction);
    }

    public Expression computeIfPresent(Variable key,
                                       BiFunction<? super Variable, ? super Expression, ? extends Expression> remappingFunction) {
        return parameters.computeIfPresent(key, remappingFunction);
    }

    public Expression compute(Variable key,
                              BiFunction<? super Variable, ? super Expression, ? extends Expression> remappingFunction) {
        return parameters.compute(key, remappingFunction);
    }

    public Expression merge(Variable key, Expression value,
                            BiFunction<? super Expression, ? super Expression, ? extends Expression> remappingFunction) {
        return parameters.merge(key, value, remappingFunction);
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof Parameters)) return false;
        final Parameters other = (Parameters) o;
        if (!other.canEqual((Object) this)) return false;
        final Object this$parameters = this.parameters;
        final Object other$parameters = other.parameters;
        if (this$parameters == null ? other$parameters != null : !this$parameters.equals(other$parameters))
            return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        final Object $parameters = this.parameters;
        result = result * PRIME + ($parameters == null ? 43 : $parameters.hashCode());
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof Parameters;
    }

    public String toString() {
        return "edu.kit.iti.algover.script.ast.Parameters(parameters=" + this.parameters + ")";
    }
}
