/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.util.AbstractCollection;
import java.util.Collection;
import java.util.Iterator;
import java.util.NoSuchElementException;

import nonnull.NonNull;
import nonnull.Nullable;

/**
 * The Class ImmutableList captures an CONS/NIL style linked list with one-way
 * pointers.
 *
 * The lists are immutable and memory can be shared by instances if they use the
 * same tail.
 *
 * The numbering of the elements begins at the far end, i.e., elements are
 * <b>appended</b> not prepended. The "tail" pointer and the "head" therefore point
 * to the lower-indexed elements and the last element of the list, respectively.
 *
 * @param <T>
 *            the payload type for the list
 *
 * @author Mattias Ulbrich
 */
@NonNull
public class ImmutableList<T> implements Iterable<T> {

    /**
     * The Constant NIL is the empty list. It is the only empty list around.
     *
     * In iterations, NIL should be used as guard condition. The payload of the
     * NIL object is void.
     */
    private static final ImmutableList<Object> NIL = new ImmutableList<>();

    /**
     * The payload data of this node.
     */
    private @Nullable final T data;

    /**
     * The length of the list. (redundant)
     */
    private final int size;

    /**
     * The tail of the linked list
     */
    private @Nullable final ImmutableList<T> tail;

    /*
     * Used to create the #NIL object.
     */
    private ImmutableList() {
        this.data = null;
        this.tail = null;
        this.size = 0;
    }

    /**
     * Instantiates a new list with by appending data.
     *
     * @param data the data to add, may be <code>null</code>
     * @param tail the tail, not <code>null</code>
     */
    public ImmutableList(@Nullable T data, @NonNull ImmutableList<T> tail) {
        this.data = data;
        this.tail = tail;
        this.size = tail.size + 1;
    }

    /**
     * Append one data element to the list.
     *
     * Existing lists are not modified, but a new list is returned.
     *
     * @param data
     *            the data to append
     *
     * @return a fresh list which has this list as tail and data as payload.
     */
    public ImmutableList<T> append(T data) {
        return new ImmutableList<T>(data, this);
    }

    /**
     * Append a collection of elemnets to the list.
     *
     * The resulting list contains all elements of this list and then all
     * elements of the provided argument, in order of iteration.
     *
     * A call to this method is as good as iterating over the argument
     * and repeatedly calling {@link #append(Object)}.
     *
     * @param iterable the collection of data to add.
     *
     * @return a fresh list which contains all elements of this list and
     * then all elements of <code>iterable</code>
     */
    public ImmutableList<T> appendAll(@NonNull Iterable<T> iterable) {
        ImmutableList<T> result = this;
        for (T elem : iterable) {
            result = result.append(elem);
        }
        return result;
    }

    public boolean isEmpty() {
        return size() == 0;
    }

    /*
     * The iterator - It simply keeps a pointer which is advanced.
     */
    private static class Itr<T> implements Iterator<T> {

        /**
         * the currently active list fragement. Next value is its head.
         */
        private ImmutableList<T> ptr;

        public Itr(ImmutableList<T> ptr) {
            this.ptr = ptr;
        }

        @Override
        public boolean hasNext() {
            return ptr != NIL;
        }

        @Override
        public T next() {
            T result = ptr.data;
            ptr = ptr.tail;
            return result;
        }

        /** {@inheritDoc}
         * <P> Removal is not supported in this class.
         */
        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }

    }

    /*
     * Caution: Since the iteration begins at the head and iterates through
     * the tail, the list must be reversed first to keep the original order.
     */
    @Override
    public Iterator<T> iterator() {
        return new Itr<T>(reverse());
    }

    /**
     * Get the number of elements in this list
     *
     * @return the size of the list.
     */
    public int size() {
        return size;
    }

    /**
     * Get an empty list of a certain type.
     *
     * @param <T> the generic type t
     * @return the immutable empty list of T
     */
    @SuppressWarnings("unchecked")
    public static <T> ImmutableList<T> nil() {
        return (ImmutableList<T>) NIL;
    }

    /**
     * Create a singleton list of the argument
     *
     * @param <T> the generic type
     * @param o the single data
     * @return the immutable list containing only o.
     */
    public static <T> ImmutableList<T> single(T o) {
        return ImmutableList.<T>nil().append(o);
    }

    /**
     * Iterate through the iterable to create a list.
     *
     * The resulting list has the same order as the argument.
     *
     * @param <T> the generic type
     * @param iterable the iterable
     * @return the immutable list
     */
    public static <T> ImmutableList<T> from(Iterable<T> iterable) {
        ImmutableList<T> result = ImmutableList.<T>nil();
        for (T t : iterable) {
            result = result.append(t);
        }
        return result;
    }

    /**
     * Iterate through the array to create a list.
     *
     * The resulting list has the same order as the argument.
     *
     * @param <T> the generic type
     * @param array the non-<code>null</code> array
     * @return the immutable list
     */
    public static <T> ImmutableList<T> from(@SuppressWarnings("unchecked") T... array) {
        ImmutableList<T> result = ImmutableList.<T>nil();
        for (T t : array) {
            result = result.append(t);
        }
        return result;
    }

    /**
     * Get a list that contains the same elements but in reverse order, i.e.,
     * <pre>
     *     get(i) == reverse().get(size() - 1 - i)
     * </pre>
     * for all {@code 0 <= i < size()}.
     *
     * @return a fresh list with reversed order
     */
    public ImmutableList<T> reverse() {
        ImmutableList<T> result = nil();
        ImmutableList<T> ptr = this;

        while(ptr != NIL) {
            result = result.append(ptr.data);
            ptr = ptr.tail;
        }

        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof ImmutableList) {
            ImmutableList<?> list = (ImmutableList<?>) obj;
            if(size() != list.size()) {
                return false;
            }
            Iterator<?> it = iterator();
            Iterator<?> it2 = list.iterator();
            while(it.hasNext()) {
                if(!it.next().equals(it2.next())) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    @Override
    public int hashCode() {
        int hc = 0;
        if(data != null) {
            hc = data.hashCode();
        }
        if(tail != null) {
            hc += 13 * tail.hashCode();
        }
        return hc;
    }

    /**
     * Returns <tt>true</tt> if this immutable list contains the specified
     * element. More formally, returns <tt>true</tt> if and only if it
     * contains an element <tt>e</tt> such that
     * <tt>(t==null&nbsp;?&nbsp;t==null&nbsp;:&nbsp;t.equals(e))</tt>.
     *
     * @param t element whose presence in this list is to be tested
     * @return <tt>true</tt> if this list contains the specified element
     */
    public boolean contains(T t) {
        for (T t2 : this) {
            if(t == null ? t2 == null : t.equals(t2)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Get this object seen as a {@link Collection} object.
     *
     * To interact with the JDK framework, this list can also
     * be seen as an immutable collection.
     *
     * @return a fresh wrapper around this object with same size and iteration order.
     */
    public Collection<T> asCollection() {
        return new AbstractCollection<T>() {

            @Override
            public Iterator<T> iterator() {
                return ImmutableList.this.iterator();
            }

            @Override
            public int size() {
                return ImmutableList.this.size();
            }
        };
    }

    /**
     * Returns a string representation of this list.
     *
     * The string representation consists of a list of the collection's elements
     * in the order they are returned by its iterator, enclosed in square
     * brackets (<tt>"[]"</tt>).  Adjacent elements are separated by the
     * characters <tt>", "</tt> (comma and space).  Elements are converted to
     * strings as by {@link String#valueOf(Object)}.
     *
     * @return a string representation of this immutable list.
     */
    @Override
    public String toString() {
        return asCollection().toString();
    }

    /**
     * Get the element at position index from the list.
     *
     * The 0th element is first appended element, while the size()-1-th element
     * is the most recently appended one.
     *
     * @param index the index to retrieve, {@code 0 <= index < size()}
     * @return the element at that index
     * @throws IndexOutOfBoundsException if the index is either negative or
     *                                   beyond the list size.
     */
    public T get(int index) {
        return takeFirst(index + 1).data;
    }

    /**
     * Returns the sub list containing the first {@code n} elements of this list
     * (in iteration order).
     *
     * <p>Technically, this method, cals {@link #getTail()} {@code size() - n}
     * times. </p>
     *
     * @param n an integer with {@code 0 <= n <= size()}
     * @return an immutable sub list of length {@code n}
     * @throws IndexOutOfBoundsException if {@code 0 > n || n > size()}
     */
    public ImmutableList<T> takeFirst(int n) {
        return dropLast(size - n);
    }

    /**
     * Returns the sub list containing all but the last {@code n} elements of
     * this list (in iteration order).
     *
     * <p>Technically, this method, cals {@link #getTail()} {@code n} times.
     * </p>
     *
     * @param n an integer with {@code 0 <= n <= size()}
     * @return an immutable sub list of length {@code n}
     * @throws IndexOutOfBoundsException if {@code 0 > n || n > size()}
     */
    public ImmutableList<T> dropLast(int n) {
        if(n < 0) {
            throw new IndexOutOfBoundsException();
        }

        ImmutableList<T> p = this;
        while(n > 0 && p != null) {
            p = p.tail;
            n --;
        }

        if(p == null) {
            throw new IndexOutOfBoundsException();
        }

        return p;
    }

    public ImmutableList<T> getTail() {
        return tail;
    }

    /**
     * Returns the sub list containing a sub range of the elements of this list.
     * For admissible values for {@code from} and {@code to}, the result is the
     * list of values
     * <pre>
     *     [ this.get(from), this.get(from+1), ..., this.get(from + len - 1) ]
     * </pre>
     *
     * @param from the first index to incorporate in the resulting list
     * @param len  the number of elements to take into the resulting list.
     * @return an immutable sub list of length {@code len}
     * @throws IndexOutOfBoundsException if {@code from < 0 || len < null ||
     *                                   from+len > size()}
     */
    public ImmutableList<T> subList(int from, int len) {

        if(from == 0) {
            return takeFirst(len);
        }

        if(from < 0 || len < 0) {
            throw new IndexOutOfBoundsException();
        }

        ImmutableList<T> p = takeFirst(from + len);
        ImmutableList<T> result = nil();

        for (int i = 0; i < len; i++) {
            result = result.append(p.data);
            p = p.getTail();
        }

        return result.reverse();
    }

    /**
     * Returns the head of this linked list.
     *
     * Please use method {@link #getLast()} instead as this better shows the
     * placement of the returned element.
     *
     * @return the last element of this list.
     * @throws NoSuchElementException if this list is empty.
     */
    @Deprecated
    public T getHead() {
        return getLast();
    }

    /**
     * Returns the last element of this list.
     *
     * @return the last element of this list.
     * @throws NoSuchElementException if this list is empty.
     */
    public T getLast() {
        if(size == 0) {
            throw new NoSuchElementException();
        }

        return data;
    }

    /**
     * Produces a new list by applying a function to the elements of this list.
     *
     * The resulting list is as if invocating
     * <pre>
     *     [ function.apply(get(0)), ..., function.apply(get(size()-1)) ]
     * </pre>
     *
     * @param function the function to apply to the elments of the list
     * @param <U>      The result type of the function, the content type for the
     *                 resulting list.
     * @param <E>      The type of exceptions that are potentially thrown by
     *                 function.
     * @return a freshly created list of the same length as this.
     * @throws E if the function application throws an exception.
     */
    public <U, E extends Exception> ImmutableList<U> map(@NonNull FunctionWithException<T, U, E> function) throws E {
        ImmutableList<U> result = nil();
        for (T el : this) {
            result = result.append(function.apply(el));
        }
        return result;
    }


    /**
     * Produces a new list by applying a function to the elements of this list
     * followed by a flattening of their contents.
     *
     * The resulting list is as if invocating
     * <pre>
     *     function.apply(get(0))
     *       .appendAll(function.apply(get(1)))
     *       .appendAll(function.apply(get(2)))
     *       . ...
     *       .appendAll(function.apply(get(size()-1)))
     * </pre>
     *
     * @param function the function to apply to the elments of the list
     * @param <U>      The result type of the function, the content type for the
     *                 resulting list.
     * @param <E>      The type of exceptions that are potentially thrown by
     *                 function.
     * @return a freshly created list of the same length as this.
     * @throws E if the function application throws an exception.
     */
    public <U, E extends Exception> ImmutableList<U> flatMap(FunctionWithException<T, Iterable<U>, E> function) throws E {
        ImmutableList<U> result = nil();
        for (T el : this) {
            result = result.appendAll(function.apply(el));
        }
        return result;
    }

    /**
     * Produces a new list by that selects only those elements from this list
     * which satisfy a predicate.
     *
     * @param predicate the function used to compute the filtration
     * @param <E>       The type of exceptions that are potentially thrown by
     *                  function.
     * @return a freshly created list which contains only the filtered elements.
     * @throws E if the function application throws an exception.
     */
    public <E extends Exception> ImmutableList<T> filter(FunctionWithException<T, Boolean, E> predicate) throws E {
        ImmutableList<T> result = nil();
        for (T el : this) {
            if(predicate.apply(el)) {
                result = result.append(el);
            }
        }
        return result;
    }

    /**
     * Returns the first element in this list that satisfies the specified
     * predicate. First element means the element with the lowest iteration
     * index.
     *
     * @param predicate the function used to check acceptance
     * @param <E>       The type of exceptions that are potentially thrown by
     *                  function.
     * @return the first element in this list satifying {@code predicate},
     * {@code null} if no element satisfies the predicate.
     * @throws E if the function application throws an exception.
     */
    public @Nullable <E extends Exception> T findFirst(FunctionWithException<T, Boolean, E> predicate) throws E {
        for (T el : this) {
            if(predicate.apply(el)) {
                return el;
            }
        }
        return null;
    }

    /**
     * Returns the last element in this list that satisfies the specified
     * predicate. Last element means the element with the highest iteration
     * index.
     *
     * @param predicate the function used to check acceptance
     * @param <E>       The type of exceptions that are potentially thrown by
     *                  function.
     * @return the last element in this list satifying {@code predicate},
     * {@code null} if no element satisfies the predicate.
     * @throws E if the function application throws an exception.
     */
    public @Nullable <E extends Exception> T findLast(FunctionWithException<T, Boolean, E> predicate) throws E {
        ImmutableList<T> l = this;
        while(l.tail != null) {
            if(predicate.apply(l.data)) {
                return l.data;
            }
            l = l.tail;
        }
        return null;
    }

}
