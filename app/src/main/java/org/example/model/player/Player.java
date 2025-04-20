package org.example.model.player;

import org.example.model.Balls;
import org.example.model.Board;

/**
 * A player abstract class.
 */
public abstract class Player {
    private final String name;
    private final Balls ball;

    /**
     * This is the constructor for the Player object.
     * @param name the name of the player.
     */
    public Player(String name, Balls ball) {
        this.name = name;
        this.ball = ball;
    }
    /**
     * This method will ask the user for the input of where he would like to place a ball.
     * @return an integer that is the location where the Ball will be added.
     */
    public abstract int[] getMove(Board board);
    /*@ pure */
    public String getName() {
        return this.name;
    }
    /*@ pure */
    public Balls getBall() {
        return this.ball;
    }
}
