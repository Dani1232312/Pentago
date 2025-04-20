package exceptions;

import java.io.Serial;

public class TooFewArguments extends Exception {
    @Serial
    private static final long serialVersionUID = -6696433070077783804L;

    public TooFewArguments(String message) {
        super(message);
    }
}
