package edu.kit.iti.algover.util.sealable;

public class SealedException extends RuntimeException {
    public SealedException() {
    }

    public SealedException(String message) {
        super(message);
    }

    public SealedException(String message, Throwable cause) {
        super(message, cause);
    }

    public SealedException(Throwable cause) {
        super(cause);
    }

    public SealedException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }
}
