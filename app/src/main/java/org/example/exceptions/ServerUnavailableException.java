package org.example.exceptions;

import java.io.Serial;

public class ServerUnavailableException extends Exception {
    @Serial
    private static final long serialVersionUID = 1L;

    public ServerUnavailableException(String s) {
        super(s);
    }
}
