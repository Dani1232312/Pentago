package model;

/**
 * This class contains the model of the Balls for the game.
 */
public enum Balls {
    /**
     * A black Ball.
     */
    BLACK(0),
    /**
     * An empty space.
     */
    EMPTY(-1),
    /**
     * A white Ball.
     */
    WHITE(1);

    private final int index;

    /**
     * The constructor that initializes the Ball object.
     * @param index based on the type of Ball black=0, white=1 and empty=-1
     */
    Balls(int index) {
        this.index = index;
    }

    /**
     * This method returns the ball on an index.
     * @param index index of the ball
     * @return a ball
     */
    //@ requires index >= -1 && index <=1;
    public static Balls indexToBall(int index) {
        for (Balls m : values()) {
            if (m.index == index) {
                return m;
            }
        }
        return null;
    }

    public static final String DISTANCE = "  ";
    public static final String B = " \u001b[30m";
    public static final String W = " \u001b[37m";
    public static final String E = " \u001b[37m";
    public static final String ANSI_RESET = "\u001B[0m";

    public String getNumColor() {
        return switch (this) {
            case BLACK -> B + "⚫" + ANSI_RESET;
            case EMPTY -> E + "⚪" + ANSI_RESET;
            case WHITE -> W + "⚫" + ANSI_RESET;
        };
    }

}
