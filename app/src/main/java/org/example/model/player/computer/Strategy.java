package org.example.model.player.computer;

import org.example.model.Balls;
import org.example.model.Board;

/**
 * A interface to differentiate strategies.
 */
public interface Strategy {
    String getName();

    /**
     * A function to determine a move for different types of players.
     * @param board a board to make the move on.
     * @param balls the ball the player has.
     * @return a valid move on the board.
     */
    int[] determineMove(Board board, Balls balls);
}
