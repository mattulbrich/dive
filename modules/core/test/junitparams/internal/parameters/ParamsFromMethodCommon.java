package junitparams.internal.parameters;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;

import junitparams.NamedParameters;
import org.junit.runners.model.FrameworkMethod;

import junitparams.Parameters;
import junitparams.internal.parameters.toarray.ParamsToArrayConverter;

class ParamsFromMethodCommon {
    private final FrameworkMethod frameworkMethod;

    ParamsFromMethodCommon(FrameworkMethod frameworkMethod) {
        this.frameworkMethod = frameworkMethod;
    }

    Object[] paramsFromMethod(Class<?> sourceClass) {
        String methodAnnotation = frameworkMethod.getAnnotation(Parameters.class).method();

        if (methodAnnotation.isEmpty()) {
            return invokeMethodWithParams(defaultMethodName(), sourceClass);
        }

        List<Object> result = new ArrayList<Object>();
        for (String methodName : methodAnnotation.split(",")) {
            for (Object param : invokeMethodWithParams(methodName.trim(), sourceClass))
                result.add(param);
        }

        return result.toArray();
    }

    Object[] paramsFromNamedMethod(Class<?> sourceClass) {
        String namedMethodAnnotation = frameworkMethod.getAnnotation(Parameters.class).named();

        if (namedMethodAnnotation.isEmpty()) {
            return invokeMethodWithParams(defaultMethodName(), sourceClass);
        }

        List<Object> result = new ArrayList<Object>();
        for (String name : namedMethodAnnotation.split(",")) {
            for (Object param : invokeNamedMethodWithParams(name.trim(), sourceClass))
                result.add(param);
        }

        return result.toArray();
    }

    boolean containsDefaultParametersProvidingMethod(Class<?> sourceClass) {
        return findMethodInTestClassHierarchy(defaultMethodName(), sourceClass) != null;
    }

    private String defaultMethodName() {
        return "parametersFor" + frameworkMethod.getName().substring(0, 1).toUpperCase()
                + this.frameworkMethod.getName().substring(1);
    }

    private Object[] invokeMethodWithParams(String methodName, Class<?> sourceClass) {
        Method providerMethod = findMethodInTestClassHierarchy(methodName, sourceClass);
        if (providerMethod == null) {
            throw new RuntimeException("Could not find method: " + methodName + " so no params were used.");
        }

        return invokeParamsProvidingMethod(providerMethod, sourceClass);
    }

    private Object[] invokeNamedMethodWithParams(String name, Class<?> sourceClass) {
        Method providerMethod = findNamedMethodInTestClassHierarchy(name, sourceClass);
        if (providerMethod == null) {
            throw new RuntimeException("Could not find method with NamedParameters annotation: " + name + " so no params were used.");
        }

        return invokeParamsProvidingMethod(providerMethod, sourceClass);
    }

    @SuppressWarnings("unchecked")
    private Object[] invokeParamsProvidingMethod(Method provideMethod, Class<?> sourceClass) {
        try {
            Object testObject = sourceClass.newInstance();
            provideMethod.setAccessible(true);
            Object result = provideMethod.invoke(testObject);

            return new ParamsToArrayConverter(frameworkMethod).convert(result);

        } catch (ClassCastException e) {
            throw new RuntimeException(
                "The return type of: " + provideMethod.getName() + " defined in class " + sourceClass +
                " should be one of the following:\nObject[][], Iterable<Object[]>, Iterable<Iterable<Object>>," +
                " Iterator<Object[]>.\nFix it!", e);
        } catch (Exception e) {
            throw new RuntimeException("Could not invoke method: " + provideMethod.getName() + " defined in class " +
                    sourceClass + " so no params were used.", e);
        }
    }

    private Method findMethodInTestClassHierarchy(String methodName, Class<?> sourceClass) {
        Class<?> declaringClass = sourceClass;
        while (declaringClass.getSuperclass() != null) {
            try {
                return declaringClass.getDeclaredMethod(methodName);
            } catch (Exception ignore) {
            }
            declaringClass = declaringClass.getSuperclass();
        }
        return null;
    }

    private Method findNamedMethodInTestClassHierarchy(String name, Class<?> sourceClass) {
        Class<?> declaringClass = sourceClass;
        while (declaringClass.getSuperclass() != null) {
            try {
                Method[] methods = declaringClass.getDeclaredMethods();
                for (Method method : methods) {
                    if (method.isAnnotationPresent(NamedParameters.class) && name.equals(method.getAnnotation(NamedParameters.class).value())) {
                        return method;
                    }
                }
            } catch (Exception ignore) {
            }
            declaringClass = declaringClass.getSuperclass();
        }
        return null;
    }
}
