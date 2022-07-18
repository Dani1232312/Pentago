package model.player;

import model.Balls;
import model.Board;
import model.player.computer.NaiveStrategy;
import model.player.computer.Strategy;

/**
 * A type of player class.
 */
public class ComputerPlayer extends Player {
    private final Strategy strategy;

    public ComputerPlayer(Balls balls) {
        super("NaiveStrategy-" + balls.toString(), balls);
        strategy = new NaiveStrategy();
    }

    public ComputerPlayer(Balls balls, Strategy strategy) {
        super(strategy.getName() + "-" + balls.toString(), balls);
        this.strategy = strategy;
    }

    @Override
    public int[] getMove(Board board) {
        return strategy.determineMove(board, this.getBall());
    }
}
