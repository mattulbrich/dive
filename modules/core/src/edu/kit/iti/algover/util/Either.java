package edu.kit.iti.algover.util;

import java.util.Objects;
import java.util.function.Function;

// TODO Documentation
public final class Either<L, R> {

    private final Object element;
    private final boolean ofLeftType;

    private Either(Object element, boolean ofLeftType) {
        this.element = element;
        this.ofLeftType = ofLeftType;
    }

    public static <L, R> Either<L, R> left(L element) {
        return new Either<>(element, true);
    }

    public static <L, R> Either<L, R> right(R element) {
        return new Either<>(element, false);
    }

    public <T> T map(Function<? super L, ? extends T> lFunc,
                     Function<? super R, ? extends T> rFunc) {
        if(ofLeftType) {
            return lFunc.apply(getLeft());
        } else {
            return rFunc.apply(getRight());
        }
    }

    @SuppressWarnings("unchecked")
    public L getLeft() {
        if(!isLeft()) {
            throw new IllegalStateException();
        }
        return (L)element;
    }

    @SuppressWarnings("unchecked")
    public R getRight() {
        if(!isRight()) {
            throw new IllegalStateException();
        }
        return (R)element;
    }

    @SuppressWarnings("unchecked")
    public <T> Either<T, R> mapLeft(Function<? super L, ? extends T> lFunc) {
        if (isLeft()) {
            return Either.left(lFunc.apply(getLeft()));
        } else {
            return (Either<T, R>)this;
        }
    }

    @SuppressWarnings("unchecked")
    public <T> Either<L,T> mapRight(Function<? super R, ? extends T> lFunc) {
        if (isRight()) {
            return (Either<L,T>)this;
        } else {
            return Either.right(lFunc.apply(getRight()));
        }
    }

    public boolean isLeft() {
        return ofLeftType;
    }

    public boolean isRight() {
        return !ofLeftType;
    }

    public Object get() {
        return element;
    }

    @Override
    public String toString() {
        return Objects.toString(element);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Either<?, ?> either = (Either<?, ?>) o;
        return ofLeftType == either.ofLeftType &&
                Objects.equals(element, either.element);
    }

    @Override
    public int hashCode() {
        return Objects.hash(element, ofLeftType);
    }
}