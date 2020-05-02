/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;
import java.net.URLConnection;
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.Charset;
import java.util.AbstractList;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.RandomAccess;
import java.util.Set;
import java.util.function.Function;

import edu.kit.iti.algover.proof.PVC;
import nonnull.NonNull;

/**
 * The Class Util is a collection of general purpose static methods.
 *
 * @author mattias ulbrich
 */
public final class Util {


    private Util() {
        throw new Error();
    }

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
    public static String commatize(@NonNull Iterable<?> list) {
        // Checkstyle: IGNORE MultipleStringLiterals
        return join(list, ", ");
    }

    /**
     * Join the string representation of a list of objects into one string,
     * separated by ", ".
     *
     * @param array
     *            some array
     *
     * @return the concatenated string, separated by commas
     */
    public static String commatize(@NonNull Object[] array) {
        return commatize(Arrays.asList(array));
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

    public static <E, F, Ex extends Exception> List<F> map(Iterable<E> input, FunctionWithException<E, F, Ex> function) throws Ex {
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

    public static String stripQuotes(String text) {
        StringBuilder sb = new StringBuilder(text);
        if(text.startsWith("\"") || text.startsWith("'")) {
            sb.deleteCharAt(0);
        }
        if(text.endsWith("\"") || text.endsWith("'")) {
            sb.deleteCharAt(sb.length() - 1);
        }
        return sb.toString();
    }

    @SuppressWarnings("unchecked")
    public static <E> Set<E> asSet(E... es) {
        return new HashSet<E>(Arrays.asList(es));
    }

    /**
     * Create a (mutable fresh hash) map from a a collection of values.
     *
     * Each value is added to the map. The key that is used is computed by the
     * function f.
     *
     * If f is not injective on the collection coll, then an {@link IllegalStateException}
     * is thrown.
     * @param coll the collection to turn into a map.
     * @param f the function to compute the keys.
     * @param <K> the types of the keys (range of f)
     * @param <V> the tapyes of data (and domain of f)
     * @param <Ex> the exception type that f may throw
     * @return a map that contains all tuples {@code x |-> f(x)}
     * @throws Ex exception thrown by the function
     */
    public @NonNull static <K, V, Ex extends Exception>
    Map<K, V> toMap(@NonNull Collection<V> coll, @NonNull FunctionWithException<V, K, Ex> f) throws Ex {
        Map<K, V> result = new HashMap<>();
        for (V element : coll) {
            K key = f.apply(element);
            if (result.containsKey(key)) {
                throw new IllegalStateException("Twice the same entry");
            }
            result.put(key, element);
        }

        return result;
    }

    /**
     * Escape characters using backslashes.
     *
     * These are the usual rules for escaping text characters. This does not
     * work for tabs, newlines, etc. only for ", \ and '.
     *
     * @param string character sequence to escape
     * @return the escaped version of the sequence.
     */
    public static @NonNull String escapeString(@NonNull String string) {
        return string
                .replace("\\", "\\\\")
                .replace("\"", "\\\"")
                .replace("\"", "\\\"");
    }

    /**
     * Add quotes around a string
     * @param string any string
     * @return "string"
     * @see #stripQuotes(String)
     */
    public static String quote(String string) {
        return "\"" + string + "\"";
    }

    public static <A, B, E extends Exception> Function<A, B> runtimeException(FunctionWithException<A,B,E> f) {
        return a -> {
            try {
                return f.apply(a);
            } catch (RuntimeException ex) {
                throw ex;
            } catch (Exception ex) {
                throw new RuntimeException(ex);
            }
        };
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

    /**
     * Read the content behind a URL into a string.
     *
     * A buffer in the content length of the content of the url is created, the
     * entire content read in one go and the result used to create a String
     * object.
     *
     * The default character encoding is used to decode the string.
     *
     * This only works for resources whose size is less than
     * {@value Integer#MAX_VALUE}.
     *
     * TODO Does this really always work? Possibly add a loop!
     *
     * @param url
     *            the url to be read, must be readable
     *
     * @return a string holding the content of the url.
     *
     * @throws IOException
     *             Signals that an I/O exception has occurred.
     */
    public static String readURLAsString(URL url) throws IOException {
        URLConnection conn = url.openConnection();

        long length = conn.getContentLength();
        byte[] buffer = new byte[(int)length];
        InputStream f = null;
        try {
            f = conn.getInputStream();
            int count = f.read(buffer);
            assert count == length;
            return new String(buffer);
        } finally {
            if(f != null) {
                f.close();
            }
        }
    }

   /**
     * Read a file into a string.
     *
     * A buffer in the length of the file is created, the entire content read in
     * one go and the result used to create a String object.
     *
     * The default character encoding is used to decode the string.
     *
     * This only works for files whose size is less than {@value Integer#MAX_VALUE}.
     *
     * TODO Does this really always work? Possibly add a loop!
     *
     * @param file
     *            the file to be read, must be readable
     *
     * @return a string holding the content of the file.
     *
     * @throws IOException
     *             Signals that an I/O exception has occurred.
     */
    public static @NonNull String readFileAsString(@NonNull File file) throws java.io.IOException{
        long length = file.length();
        byte[] buffer = new byte[(int)length];
        try(FileInputStream f = new FileInputStream(file)) {
            int count = f.read(buffer);
            assert count == length;
            return new String(buffer);
        }
    }

    /**
     * Save a string to a file.
     *
     * Default character encoding is used.
     *
     * @param string String to save
     * @param file file to write to
     * @throws IOException if file cannot be written or no access.
     */
    public static void saveStringAsFile(@NonNull String string, @NonNull File file) throws IOException {
        try (FileWriter fw = new FileWriter(file)) {
            fw.write(string);
        }
    }

    /**
     * Mask a file name to be universally usable on filesystems.
     *
     * In particular this is used to mask {@link PVC#getIdentifier()}.
     *
     * Alphanumeric characters ({@code A-Za-z0-9}) and some other characters are
     * taken verbatim. Spaces become "-", and "/" becomes "+".
     *
     * @param s
     *            the string to masked
     * @return the masked string
     */
    public static String maskFileName(String s) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (('0' <= c && c <= '9') || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
                    || "_[]().,;".indexOf(c) >= 0) {
                sb.append(c);
            } else {
                switch (c) {
                    case ' ':
                        sb.append("-");
                        break;
                    case '/':
                        sb.append("+");
                        break;
                    default:
                        ByteBuffer bb = Charset.forName("UTF-8").encode(Character.toString(c));
                        while (bb.hasRemaining()) {
                            sb.append(String.format("%%%02x", bb.get()));
                        }
                }
            }
        }

        return sb.toString();
    }

    /**
     * Remove duplicates from a collection. Only the first occurrence is kept.
     * Requires that the elements of the list implement equals nad hashcode.
     * Requires that the iterator supports removce.
     * ...
     */
    public static <T> void removeDuplicates(Collection<T> coll) {
        Set<T> seen = new HashSet<T>();
        Iterator<T> it = coll.iterator();
        while(it.hasNext()) {
            T t = it.next();
            if(seen.contains(t)) {
                it.remove();
            } else {
                seen.add(t);
            }
        }
    }


    /**
     * Remove duplicates from a collection. Only the first occurrence is kept.
     * Requires that the elements of the list implement equals nad hashcode.
     * Requires that the iterator supports removce.
     * ...
     */
    public static <T> boolean hasDuplicates(Collection<T> coll) {
        Set<T> seen = new HashSet<T>();
        for (T t : coll) {
            if (seen.containsAll(coll))
                return true;
            seen.add(t);
        }
        return false;
    }

}
