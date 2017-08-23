/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.util.AbstractCollection;
import java.util.Collection;
import java.util.Iterator;
import java.util.function.Function;

import edu.kit.iti.algover.term.Sequent;

/**
 * The Class ImmutableList captures an CONS/NIL style linked list with one-way
 * pointers.
 *
 * The lists are immutable and memory can be shared by instances if they use the
 * same tail.
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
     * The payload data of the head.
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
     * Instantiates a new list with by prepending data to the tail.
     *
     * @param data the data
     * @param tail the tail, not <code>null</code>
     */
    public ImmutableList(T data, ImmutableList<T> tail) {
        super();
        this.data = data;
        this.tail = tail;
        this.size = tail.size + 1;
    }

    /**
     * Prepend one data element to the list.
     *
     * Existing lists are not modified but a new list is returned.
     *
     * @param data
     *            the data to prepend
     * @return a fresh list which has this list as tail and data as payload.
     */
    public ImmutableList<T> append(T data) {
        return new ImmutableList<T>(data, this);
    }

    public ImmutableList<T> appendAll(Iterable<T> iterable) {
        ImmutableList<T> result = this;
        for(T elem : iterable) {
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

    @Override
    public Iterator<T> iterator() {
        return new Itr<T>(reverse());
    }

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

    public T get(int index) {

        int count = size - 1 - index;

        if(count < 0) {
            throw new IndexOutOfBoundsException();
        }

        ImmutableList<T> p = this;
        while(count > 0 && p != null) {
            p = p.tail;
            count --;
        }

        if(p == null) {
            throw new IndexOutOfBoundsException();
        }

        return p.data;
    }

    public ImmutableList<T> getTail() {
        return tail;
    }

    public T getHead() {
        return data;
    }

    public <U> ImmutableList<U> map(Function<T, U> function) {
        ImmutableList<U> result = nil();
        for (T el : this) {
            result = result.append(function.apply(el));
        }
        return result;
    }
}
