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
public class Signature extends ASTNode<ScriptLanguageParser.ArgListContext> implements Map<Variable, Type> {
    private final Map<Variable, Type> sig = new LinkedHashMap<>();

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public Signature copy() {
        Signature signature = new Signature();
        forEach((k, v) -> signature.put(k.copy(), v));
        return signature;
    }

    public int size() {
        return sig.size();
    }

    public boolean isEmpty() {
        return sig.isEmpty();
    }

    public boolean containsKey(Object key) {
        return sig.containsKey(key);
    }

    public boolean containsValue(Object value) {
        return sig.containsValue(value);
    }

    public Type get(Object key) {
        return sig.get(key);
    }


    public Type get(Variable key) {
        return sig.get(key);
    }

    public Type put(Variable key, Type value) {
        return sig.put(key, value);
    }

    public Type remove(Object key) {
        return sig.remove(key);
    }

    public void putAll(Map<? extends Variable, ? extends Type> m) {
        sig.putAll(m);
    }

    public void clear() {
        sig.clear();
    }

    public Set<Variable> keySet() {
        return sig.keySet();
    }

    public Collection<Type> values() {
        return sig.values();
    }

    public Set<Entry<Variable, Type>> entrySet() {
        return sig.entrySet();
    }

    public Type getOrDefault(Object key, Type defaultValue) {
        return sig.getOrDefault(key, defaultValue);
    }

    public void forEach(BiConsumer<? super Variable, ? super Type> action) {
        sig.forEach(action);
    }

    public void replaceAll(BiFunction<? super Variable, ? super Type, ? extends Type> function) {
        sig.replaceAll(function);
    }

    public Type putIfAbsent(Variable key, Type value) {
        return sig.putIfAbsent(key, value);
    }

    public boolean remove(Object key, Object value) {
        return sig.remove(key, value);
    }

    public boolean replace(Variable key, Type oldValue, Type newValue) {
        return sig.replace(key, oldValue, newValue);
    }

    public Type replace(Variable key, Type value) {
        return sig.replace(key, value);
    }

    public Type computeIfAbsent(Variable key, Function<? super Variable, ? extends Type> mappingFunction) {
        return sig.computeIfAbsent(key, mappingFunction);
    }

    public Type computeIfPresent(Variable key,
                                 BiFunction<? super Variable, ? super Type, ? extends Type> remappingFunction) {
        return sig.computeIfPresent(key, remappingFunction);
    }

    public Type compute(Variable key,
                        BiFunction<? super Variable, ? super Type, ? extends Type> remappingFunction) {
        return sig.compute(key, remappingFunction);
    }

    public Type merge(Variable key, Type value,
                      BiFunction<? super Type, ? super Type, ? extends Type> remappingFunction) {
        return sig.merge(key, value, remappingFunction);
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof Signature)) return false;
        final Signature other = (Signature) o;
        if (!other.canEqual((Object) this)) return false;
        final Object this$sig = this.sig;
        final Object other$sig = other.sig;
        if (this$sig == null ? other$sig != null : !this$sig.equals(other$sig)) return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        final Object $sig = this.sig;
        result = result * PRIME + ($sig == null ? 43 : $sig.hashCode());
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof Signature;
    }

    public String toString() {
        return "edu.kit.iti.algover.script.ast.Signature(sig=" + this.sig + ")";
    }
}
