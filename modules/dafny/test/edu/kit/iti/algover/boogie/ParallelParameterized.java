/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.boogie;

import org.junit.runners.Parameterized;
import org.junit.runners.ParentRunner;
import org.junit.runners.model.RunnerScheduler;

import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public class ParallelParameterized extends Parameterized {

    public ParallelParameterized(Class<?> klass) throws Throwable {
        super(klass);
        setScheduler(new RunnerScheduler() {
            private final ExecutorService fService = Executors.newCachedThreadPool();

            public void schedule(Runnable childStatement) {
                fService.submit(childStatement);
            }

            public void finished() {
                try {
                    fService.shutdown();
                    fService.awaitTermination(Long.MAX_VALUE, TimeUnit.NANOSECONDS);
                } catch (InterruptedException e) {
                    e.printStackTrace(System.err);
                }
            }
        });
    }
}
