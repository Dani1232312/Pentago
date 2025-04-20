package org.example.model.player.computer;

import org.example.model.Balls;
import org.example.model.Board;

/**
 * A smart strategy for the AI.
 */
public class SmartStrategy implements Strategy {
    private final Board copy = new Board();

    public SmartStrategy() {
    }

    @Override
    public String getName() {
        return "SmartStrategy";
    }

    @Override
    public int[] determineMove(Board board, Balls ball) {
        int[] result = new int[2];
        // loop the number of possible rotations
        for (int rotate = 0; rotate < 8; rotate++) {
            copy.setFields(board.copy());
            copy.rotate(rotate);
            for (int moveTry = 0; moveTry < 36; moveTry++) {
                //use the copy of the board to check the move in advance
                copy.setFields(board.copy());
                //add the ball first
                copy.move(moveTry, ball);
                //then rotate the board
                copy.rotate(rotate);
                if (copy.isWinner(ball) && board.getBall(moveTry / board.size, moveTry % board.size)
                        .equals(Balls.EMPTY)) {
                    result[0] = moveTry;
                    result[1] = rotate;
                    return result;
                }
            }
        }
        // loop the number of possible rotations
        for (int rotate = 0; rotate < 8; rotate++) {
            copy.setFields(board.copy());
            copy.rotate(rotate);
            for (int moveTry = 0; moveTry < 36; moveTry++) {
                //use the copy of the board to check the move in advance
                copy.setFields(board.copy());
                //add the ball first
                copy.move(moveTry, Balls.WHITE);
                //then rotate the board
                copy.rotate(rotate);
                //if the other ball is winning by making a move. Block him.
                if (copy.isWinner(Balls.WHITE) &&
                        board.getBall(moveTry / board.size, moveTry % board.size).
                                equals(Balls.EMPTY)) {
                    result[0] = moveTry;
                    result[1] = rotate;
                    return result;
                }
            }
        }
        //if no suitable move return a NaiveStrategy move
        result = (new NaiveStrategy()).determineMove(board, ball);
        return result;
    }
}
