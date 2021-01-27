package edu.kit.iti.algover.util.sealable;

import java.util.AbstractList;
import java.util.List;
import java.util.function.Supplier;

public class SealableList<T> extends AbstractList<T> {

    private final Supplier<Boolean> sealCheck;
    private final List<T> delegate;

    public SealableList(Supplier<Boolean> sealCheck, List<T> delegate) {
        this.sealCheck = sealCheck;
        this.delegate = delegate;
    }

    @Override
    public T get(int index) {
        return delegate.get(index);
    }

    @Override
    public int size() {
        return delegate.size();
    }

    public void add(int index, T element) {
        if(sealCheck.get()) {
            throw new SealedException();
        }
        delegate.add(index, element);
    }

    public T remove(int index) {
        if(sealCheck.get()) {
            throw new SealedException();
        }
        return delegate.remove(index);
    }

    public T set(int index, T element) {
        if (sealCheck.get()) {
            throw new SealedException();
        }
        return delegate.set(index, element);
    }
}
