package nonnull;

import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

/**
 * The annotation <code>NonNull</code> can be used to annotate methods or their
 * parameters (of reference type) to denote that the must not be null.
 *
 * If the annotation is used on an array over a reference type or over an
 * instance of the {@link Iterable} interface, the non-nullness check is
 * extended to each element of the collection. <i>Please note:</i> If the
 * content is a collection again, it is not null-checked. (Only depth 1)
 *
 * If a class is annotated DeepNonNull, all parameters and returns to all
 * methods (and constructors!) are considered annotated DeepNonNull. You can
 * declare exceptions to this default using the {@link Nullable} (or
 * {@link NonNull} if you do want exclude the "deep" aspect) annotation.
 *
 * The annotations are documented in JavaDoc.
 *
 * You can patch class files containing DeepNonNull annotations with runtime
 * checks using the class {@link NonNullPatch}
 *
 * You can use the classloader {@link NonNullClassLoader} to patch class files
 * dynamically at run time.
 */

public
    @Documented
    @Retention(RetentionPolicy.RUNTIME)

@interface DeepNonNull {

}
