/*
 * NonNull Runtime Checking for Methods
 *
 * 2009 by Mattias Ulbrich
 *
 * published under GPL.
 */

package nonnull;
import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;


/**
 * The annotation <code>Nullable</code> can be used to annotate methods or
 * their parameters (of reference type) to denote that the *may* be null.
 * If a class is annotated NonNull, this annotation can be used to declare
 * exception of this default behaviour.
 *
 * The annotations are documented in JavaDoc.
 *
 * You can patch class files containing NonNull annotations with runtime checks
 * using the class {@link NonNullPatch}
 *
 * You can use the classloader {@link NonNullClassLoader} to patch class files
 * dynamically at run time.
 */

public
  @Documented
  @Retention(RetentionPolicy.RUNTIME)

@interface Nullable {

}
