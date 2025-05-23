package org.example.model.player.computer;

import org.example.model.Balls;
import org.example.model.Board;

import java.util.Random;

/**
 * A naive strategy for the AI.
 */
public class NaiveStrategy implements Strategy {

    public NaiveStrategy() {
    }

    @Override
    public String getName() {
        return "Naive";
    }

    @Override
    public int[] determineMove(Board board, Balls balls) {
        int[] move = new int[2];
        Random r = new Random();
        int low = 0;
        int high = 35;
        int randomMove;
        randomMove = r.nextInt(high - low) + low;
        //get a random move that is valid.
        while (board.getBall(randomMove / Board.SIZE, randomMove % Board.SIZE) == Balls.WHITE
            || board.getBall(randomMove / Board.SIZE, randomMove % Board.SIZE) == Balls.BLACK) {
            randomMove = r.nextInt(high - low) + low;
        }
        high = 7;
        int quadrant = r.nextInt(high - low) + low;
        move[0] = randomMove;
        move[1] = quadrant;
        return move;
    }
}
