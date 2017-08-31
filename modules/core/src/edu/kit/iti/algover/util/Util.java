/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.*;
import java.util.function.Function;


public final class Util {
    /**
     * Wrap an immutable list object around an array. The elements in the array
     * can by no means be replaced.
     *
     * <p>
     * The result is closely related to {@link java.util.Arrays#asList(Object...)} but is
     * unmodifiable.
     *
     * @param array
     *            some array
     *
     * @param <E>
     *            the element type of the array argument
     *
     * @return an immutable list wrapping the argument array.
     *
     * @see java.util.Arrays#asList(Object...)
     */
    public static <E> List<E> readOnlyArrayList(E[] array) {
        return readOnlyArrayList(array, 0, array.length);
    }

    /**
     * Wrap an immutable list object around a part of an array. The elements in
     * the array can by no means be replaced. Additionally, elements outside the
     * given range cannot be accessed.
     *
     * <p>
     * The range is given by to indices from and to. The first element of the
     * resulting list is the element {@code array[from]} and the last is
     * {@code array[to-1]} (to is exclusive).
     *
     * <p>
     * The following must hold for the indices:
     * {@code 0 <= from <= to <= array.length}
     *
     * @param array
     *            some array
     *
     * @param from
     *            the array index of the first element in the result list.
     *
     * @param to
     *            the array index of the last element in the result list plus 1.
     *
     * @param <E>
     *            the element type of the array argument
     *
     * @return an immutable list wrapping the argument array.
     *
     * @see java.util.Arrays#asList(Object...)
     */
    public static <E> List<E> readOnlyArrayList(E[] array, int from, int to) {
        return new ReadOnlyArrayList<E>(array, from, to);
    }

    /**
     * Create an array containing the elements of a collection. The method name
     * is misleading.
     *
     * <p>
     * This method is type safe. The type of the contents of the array must be
     * compatible with the types of the elements in the array.
     *
     * @param collection
     *            the collection to be saved in an array.
     *
     * @param clss
     *            the class of the array to create.
     * @param <E>
     *            the class type of the resulting array
     *
     * @return an array whose content type is the specified class, whose length
     *         is the size of the collection and whose contents is the one of
     *         the collection as if retrieved by
     *         {@link Collection#toArray(Object[])}.
     */
    @SuppressWarnings({ "unchecked" })
    public static <E extends Object> E[] toArray(
            Collection<? extends E> collection,
            Class<E> clss) {

        E[] array = (E[]) java.lang.reflect.Array.newInstance(clss, collection.size());
        return collection.toArray(array);

    }

    /**
     * Join the string representation of a list of objects into one string,
     * separated by ", ".
     *
     * @param list
     *            some list
     *
     * @return the concatenated string, separated by commas
     */
    public static String commatize(Iterable<?> list) {
        // Checkstyle: IGNORE MultipleStringLiterals
        return join(list, ", ");
    }

    /**
     * Join a collection of objects into a string, separated by some separating
     * string in between them. The order in the resulting string is determined
     * by the order of the iteration.
     *
     * <p>
     * If <code>ignoreNull</code> is set then only non-null elements will be
     * used in the result whose string representation is not empty.
     *
     * @param list
     *            some collection of objects
     * @param sep
     *            the separating string
     * @param ignoreNull
     *            whether <code>null</code> and empty strings are to be
     *            included.
     *
     * @return the concatenation of the objects as strings.
     */
    public static String join(Iterable<?> list, String sep, boolean ignoreNull) {
        StringBuilder sb = new StringBuilder();
        Iterator<?> it = list.iterator();
        while(it.hasNext()) {
            Object elem = it.next();
            if(!ignoreNull || elem != null) {
                String s = elem == null ? "(null)" : elem.toString();
                if(s.length() > 0) {
                    if(sb.length() > 0) {
                        sb.append(sep);
                    }
                    sb.append(s);
                }
            }
        }
        return sb.toString();
    }

    /**
     * Join a collection of objects into a string,
     * separated by some string in between them.
     * The order in the resulting string is determined by the order of
     * the iteration.
     *
     * <p>
     * On each elment in the list {@link Object#toString()} will be called.
     *
     * @param list
     *            some collection of objects
     * @param sep
     *            the separating string
     *
     * @return the concatenation of the objects as strings.
     */
    public static String join(Iterable<?> list, String sep) {
        return join(list, sep, false);
    }

    /**
     * Join an array of objects into a string separated by some string in
     * between them
     *
     * <p>
     * On each elment in the array {@link Object#toString()} will be called.
     *
     * @param array
     *            some array of objects
     * @param sep
     *            the separating string
     *
     * @return the concatenation of the objects as strings.
     */
    public static String join(Object[] array, String sep) {
        return join(readOnlyArrayList(array), sep, false);
    }

    /**
     * Duplicate a string a number of times.
     *
     * @param string
     *            the string to duplicate.
     * @param count
     *            the number of repetitions.
     *
     * @return the repeated concatenation of the argument.
     */
    public static String duplicate(String string, int count) {
        StringBuffer sb = new StringBuffer();
        for (int i = 0; i < count; i++) {
            sb.append(string);
        }
        return sb.toString();
    }

    /**
     * Drain a stream into a string.
     *
     * @param is
     *            the non-<code>null</code> input stream to drain
     * @return the string
     * @throws IOException
     *             Signals that an I/O exception has occurred.
     */
    public static String streamToString(InputStream is) throws IOException {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        drainStream(is, baos);
        return new String(baos.toByteArray());
    }

    /**
     * Drain an input stream to an output stream.
     *
     * Do not close either stream at the end.
     *
     * @param is
     *            the non-<code>null</code> input stream
     * @param os
     *            the non-<code>null</code> output stream
     * @throws IOException
     *             Signals that an I/O exception has occurred.
     */
    public static void drainStream(InputStream is, OutputStream os) throws IOException {
        byte[] buffer = new byte[4096];
        int read;

        while((read = is.read(buffer)) >= 0) {
            os.write(buffer, 0, read);
        }
    }

    public static <E, F> List<F> map(Iterable<E> input, Function<E, F> function) {
        List<F> result;
        if(input instanceof RandomAccess) {
            result = new ArrayList<>();
        } else {
            result = new LinkedList<>();
        }

        for (E e : input) {
            result.add(function.apply(e));
        }

        return result;
    }

    public static <E> E[] requireDeepNonNull(E[] array) {
        Objects.requireNonNull(array);
        for (E e : array) {
            Objects.requireNonNull(e);
        }

        return array;
    }

    public static <E extends Iterable<?>> E requireDeepNonNull(E iterable) {
        Objects.requireNonNull(iterable);
        for (Object e : iterable) {
            Objects.requireNonNull(e);
        }

        return iterable;
    }

    // TODO is there no builtin mechanism for that?
    public static <E> List<E> toList(Iterable<E> itb) {
        ArrayList<E> result = new ArrayList<>();
        itb.forEach(result::add);
        return result;
    }

    /**
     * A wrapper class for the collection framework. It renders an array into an
     * immutable list.
     *
     * @param <E> the element type of the list.
     */
    private static final class ReadOnlyArrayList<E extends Object>
            extends AbstractList<E> implements RandomAccess {
        private final E[] array;
        private final int from;
        private final int to;

        private ReadOnlyArrayList(E[] array, int from, int to) {
            if (array == null) {
                throw new NullPointerException();
            }

            if (from < 0) {
                throw new IndexOutOfBoundsException("Must be within array bounds: " + from);
            }

            if (to > array.length) {
                throw new IndexOutOfBoundsException("Must be at most array length (" +
                        array.length + "): " + from);
            }

            if (to < from) {
                throw new IndexOutOfBoundsException("Must be increasing: " +
                        from + " ... " + to);
            }

            this.from = from;
            this.to = to;
            this.array = array;
        }

        @Override
        public E get(int index) {
            return array[index + from];
        }

        @Override
        public int size() {
            return to - from;
        }

        @Override
        public E[] toArray() {
            if (from == 0 && to == array.length) {
                return array.clone();
            } else {
                @SuppressWarnings("unchecked")
                E[] result = (E[]) new Object[to - from];
                System.arraycopy(array, from, result, 0, to - from);
                return result;
            }
        }

        @Override
        public int indexOf(Object o) {
            if (o == null) {
                for (int i = from; i < to; i++) {
                    if (array[i] == null) {
                        return i - from;
                    }
                }
            } else {
                for (int i = from; i < to; i++) {
                    if (o.equals(array[i])) {
                        return i - from;
                    }
                }
            }
            return -1;
        }

        @Override
        public boolean contains(Object o) {
            return indexOf(o) != -1;
        }

    }


}
