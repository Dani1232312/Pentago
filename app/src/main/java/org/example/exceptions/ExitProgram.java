package org.example.exceptions;

import java.io.Serial;

public class ExitProgram extends Exception {
    @Serial
    private static final long serialVersionUID = 1L;

    public ExitProgram(String s) {
        super(s);
    }
}
