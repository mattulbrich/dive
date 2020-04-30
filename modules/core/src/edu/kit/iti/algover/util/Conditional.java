package edu.kit.iti.algover.util;

public abstract class Conditional {

    public static Conditional notAtFirst() {
        return new Wait(1);
    }

    public static Conditional onlyAfter(int n) {
        return new Wait(n);
    }

    public static Conditional onlyOnce() {
        return new AtMost(1);
    }

    public static Conditional onlyNTimes(int n) {
        return new AtMost(n);
    }

    private static class Wait extends Conditional {

        private int waitCycles;

        public Wait(int waitCycles) {
            this.waitCycles = waitCycles;
        }

        @Override
        public <E extends Exception> void run(ActionWithException<E> runnable) throws E {
            if (waitCycles > 0) {
                waitCycles --;
            } else {
                runnable.run();
            }
        }
    }

    private static class AtMost extends Conditional {

        private int capacity;

        public AtMost(int capacity) {
            this.capacity = capacity;
        }

        @Override
        public <E extends Exception> void run(ActionWithException<E> runnable) throws E {
            if (capacity > 0) {
                runnable.run();
                capacity --;
            }
        }
    }

    public abstract <E extends Exception> void run(ActionWithException<E> runnable) throws E;

    public interface ActionWithException<E extends Exception> {
        public void run() throws E;
    }
}
