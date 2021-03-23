package edu.kit.iti.algover.util;

import java.util.Objects;
import java.util.function.Function;

/**
 * <p>An instance of this class represents a value of one of two possible types
 * (a disjoint union or the sum type). Instances are immutable.</p>
 *
 * <p>The two possibilites are called left and right. Elements can be created
 * using
 * the according static functions {@link #left(Object)} and {@link
 * #right(Object)}. Access is then via {@link #getLeft()} and {@link
 * #getRight()}. The getters throw an {@link IllegalStateException} if called on
 * an instance of the other side. To check for the which side an instance
 * belongs to, the method {@link #isLeft()} and {@link #isRight()} can be
 * used.</p>
 *
 * <p>Typical use case is a method whose return type depends on the path that
 * is
 * taken within the method. Using an Either return, it can do so. The caller can
 * then use the object to discern the different result possibilities and access
 * the content -- in a type safe fashion.</p>
 *
 * <p>The class has some mapping functionalities ({@link #map(Function, Function)},
 * {@link #mapLeft(Function)}, {@link #mapRight(Function)}).</p>
 *
 * <h2>Example</h2>
 * Solution without Either.
 * <pre>
 * {@code
 *     Object getImportantData() {
 *         if(someExternalCondition) {
 *             return "String";
 *         } else {
 *             return 42;
 *         }
 *     }
 *
 *     // callsite:
 *     Object x = getImportantData();
 *     if(x instanceof String) {
 *         String s = (String) x
 *         ...
 *     } else {
 *         Integer i = (Integer)x;
 *         ...
 *     }
 * }
 * </pre>
 *
 * Solution with Either. It contains no explicit downcasts.
 * <pre>
 * {@code
 *     Either<String, Integer> getImportantData() {
 *         if(someExternalCondition) {
 *             return "String";
 *         } else {
 *             return 42;
 *         }
 *     }
 *
 *     // callsite:
 *     Either<> x = getImportantData();
 *     if(x.isLeft()) {
 *         String s = x.getLeft();
 *         ...
 *     } else {
 *         Integer i = x.getRight();
 *         ...
 *     }
 * }</pre>
 *
 * Another common use of Either is as an alternative to {@link
 * java.util.Optional} for dealing with possible missing values. For example,
 * you could use {@code Either<String, Int>} to detect whether a received input
 * is a String or an Int.
 *
 * @param <L> the left type
 * @param <R> the right type
 * @author Mattias Ulbrich
 */
public final class Either<L, R> {

    /**
     * The actual data is stored in a field of type Object.
     * It is only downcast when needed.
     */
    private final Object element;

    /**
     * An indicator for the side of this instance. true means left, false means
     * right.
     */
    private final boolean ofLeftType;

    /**
     * Create a new instance.
     *
     * @param element the element to be stored (may be null)
     * @param ofLeftType the side to store it into.
     */
    private Either(Object element, boolean ofLeftType) {
        this.element = element;
        this.ofLeftType = ofLeftType;
    }

    /**
     * Create a new instance of a "left" instance.
     *
     * {@link #isLeft()} will return true, {@link #getLeft()} will return {@code
     * element}. {@link #isRight()} will return false, {@link #getRight()} will
     * throw an exception.
     *
     * @param element the element to be stored (may be null)
     */
    public static <L, R> Either<L, R> left(L element) {
        return new Either<>(element, true);
    }

    /**
     * Create a new instance of a "right" instance.
     *
     * {@link #isRight()} will return true, {@link #getRight()} will return
     * {@code element}. {@link #isLeft()} will return false, {@link #getLeft()}
     * will throw an exception.
     *
     * @param element the element to be stored (may be null)
     */
    public static <L, R> Either<L, R> right(R element) {
        return new Either<>(element, false);
    }

    /**
     * Get the element inside, regardless of its type.
     * This method does not fail, but has fewer type guarantees.
     *
     * @return the stored element
     */
    public Object get() {
        return element;
    }

    /**
     * Return true iff the element has been stored for left type
     *
     * @return true iff the element is of the left type
     */
    public boolean isLeft() {
        return ofLeftType;
    }

    /**
     * Get the stored element if it was stored as a left element.
     * Throw an {@link IllegalStateException} if this is a right object.
     *
     * @return the stored element
     * @throws IllegalStateException if this is a right object.
     */
    @SuppressWarnings("unchecked")
    public L getLeft() {
        if (!isLeft()) {
            throw new IllegalStateException();
        }
        return (L) element;
    }

    /**
     * Return true iff the element has been stored for right type
     *
     * @return true iff the element is of the right type
     */
    public boolean isRight() {
        return !ofLeftType;
    }

    /**
     * Get the stored element if it was stored as a right element.
     * Throw an {@link IllegalStateException} if this is a left object.
     *
     * @return the stored element
     * @throws IllegalStateException if this is a left object.
     */
    @SuppressWarnings("unchecked")
    public R getRight() {
        if (!isRight()) {
            throw new IllegalStateException();
        }
        return (R) element;
    }

    /**
     * Apply a pair of mapping functions to this object to obtain a single value.
     *
     * Depending on the side of this object, either the first or second argument are used.
     * @param leftFunc the non-null function to be applied to left objects
     * @param rightFunc the non-null function to be applied to right objects
     * @param <T> the common result type of both arguments and of the method.
     * @return the result of the application of one of the two functions.
     */
    public <T> T map(Function<? super L, ? extends T> leftFunc,
                     Function<? super R, ? extends T> rightFunc) {
        if (ofLeftType) {
            return leftFunc.apply(getLeft());
        } else {
            return rightFunc.apply(getRight());
        }
    }

    /**
     * Apply a function to this object if it is a left object.
     *
     * The result is still an either with the left type the target type
     * of the function and the right type untouched.
     *
     * If this is a left object: The function is applied and a new Either object
     * is created and returned.
     * Otherwise: {@code this} is returned;
     *
     * @param lFunc the non-null function to be applied to left objects
     * @param <T> the result type of that function
     * @return either {@code this} or a new {@link Either} object. see above.
     */
    @SuppressWarnings("unchecked")
    public <T> Either<T, R> mapLeft(Function<? super L, ? extends T> lFunc) {
        if (isLeft()) {
            return Either.left(lFunc.apply(getLeft()));
        } else {
            return (Either<T, R>) this;
        }
    }

    /**
     * Apply a function to this object if it is a right object.
     *
     * The result is still an either with the right type the target type
     * of the function and the left type untouched.
     *
     * If this is a right object: The function is applied and a new Either object
     * is created and returned.
     * Otherwise: {@code this} is returned;
     *
     * @param lFunc the non-null function to be applied to left objects
     * @param <T> the result type of that function
     * @return either {@code this} or a new {@link Either} object. see above.
     */
    @SuppressWarnings("unchecked")
    public <T> Either<L, T> mapRight(Function<? super R, ? extends T> lFunc) {
        if (isRight()) {
            return (Either<L, T>) this;
        } else {
            return Either.right(lFunc.apply(getRight()));
        }
    }

    /**
     * Delegates to the toString method of the element.
     *
     * It is null-safe.
     *
     * @return a string representation of the element.
     */
    @Override
    public String toString() {
        return Objects.toString(element);
    }

    /**
     * Two Either instances are equal iff their elements are equal (modulo
     * {@link Object#equals(Object) equals) and they are on the same side.
     *
     * @param o the object to check against
     * @return true if this and o denote the same either object.
     */
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