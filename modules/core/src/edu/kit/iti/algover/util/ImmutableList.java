/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.util.AbstractCollection;
import java.util.Collection;
import java.util.Iterator;
import java.util.function.Function;
import java.util.function.Predicate;

import edu.kit.iti.algover.term.Sequent;

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
    private final T data;

    /**
     * The length of the list. (redundant)
     */
    private final int size;

    /**
     * The tail of the linked list
     */
    private final ImmutableList<T> tail;

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
     * @param data the data to addd, may be <code>null</code>
     * @param tail the tail, not <code>null</code>
     */
    public ImmutableList(T data, ImmutableList<T> tail) {
        super();
        this.data = data;
        this.tail = tail;
        this.size = tail.size + 1;
    }

    /**
     * Append one data element to the list.
     *
     * Existing lists are not modified but a new list is returned.
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
     * @return
     */
    public ImmutableList<T> appendAll(Iterable<T> iterable) {
        ImmutableList<T> result = this;
        for (T elem : iterable) {
            result = result.append(elem);
        }
        return result;
    }

    /*
     * The iterator - It simply keeps a pointer which is advanced.
     */
    private static class Itr<T> implements Iterator<T> {

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

    @Override
    public String toString() {
        return asCollection().toString();
    }

    /**
     * Get the element at position index from the list.
     *
     * The 0th element is first appended element, while
     * the size()-1-th element is the most recently appended one.
     *
     * @param index the index to retrieve, {@code 0 <= index < size()}
     * @return the element at that index
     * @throws IndexOutOfBoundsException if the index is either negative or beyond the list size.
     */
    public T get(int index) {
        return takeFirst(index + 1).data;
    }

    public ImmutableList<T> takeFirst(int n) {
        return dropLast(size - n);
    }

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
     * Please use {@link #getLast()} instead.
     * @return
     */
    @Deprecated
    public T getHead() {
        return getLast();
    }

    public T getLast() {
        return data;
    }

    public <U> ImmutableList<U> map(Function<T, U> function) {
        ImmutableList<U> result = nil();
        for (T el : this) {
            result = result.append(function.apply(el));
        }
        return result;
    }

    public ImmutableList<T> filter(Predicate<T> predicate) {
        ImmutableList<T> result = nil();
        for (T el : this) {
            if(predicate.test(el)) {
                result = result.append(el);
            }
        }
        return result;
    }

    public T findFirst(Predicate<T> predicate) {
        ImmutableList<T> result = nil();
        for (T el : this) {
            if(predicate.test(el)) {
                return el;
            }
        }
        return null;
    }

}
