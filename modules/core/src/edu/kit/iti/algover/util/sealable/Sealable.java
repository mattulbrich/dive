package edu.kit.iti.algover.util.sealable;

import java.util.function.Supplier;

public final class Sealable<T> {

    private T value;
    private final Supplier<Boolean> sealCheck;

    public Sealable(Supplier<Boolean> sealCheck) {
        this.sealCheck = sealCheck;
    }

    public T get() {
        return value;
    }

    public void set(T value) {
        if(sealCheck.get()) {
            throw new SealedException();
        }
        this.value = value;
    }

    public boolean isSet() {
        return value != null;
    }

    public boolean equals(Object other) {
        if(get() == null) {
            return other == null;
        }
        if(other instanceof Sealable) {
            return get().equals(((Sealable<?>) other).get());
        }
        return get().equals(other);
    }
}
