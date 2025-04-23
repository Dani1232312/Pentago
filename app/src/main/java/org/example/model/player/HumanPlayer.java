package org.example.model.player;

import org.example.exceptions.ExitProgram;
import org.example.model.Balls;

import java.util.Scanner;
import java.util.logging.Logger;

import org.example.model.Board;
import org.example.model.player.computer.NaiveStrategy;
import org.example.model.player.computer.SmartStrategy;


/**
 * A type of player class.
 */
public class HumanPlayer extends Player {
    private int difficulty = 0;
    private static final Logger LOGGER = Logger.getLogger(HumanPlayer.class.getName());

    /**
     * This is the constructor of the HumanPlayer object.
     * @param name the name of the HumanPlayer.
     */
    public HumanPlayer(String name, Balls ball) {
        super(name, ball);
    }

    @Override
    public int[] getMove(Board board) {
        int[] move = new int[2];
        LOGGER.info("It's your turn to make a move!");
        LOGGER.info("MOVE~<A>~<B>");
        try (Scanner scanner = new Scanner(System.in)) {
            while (scanner.hasNext()) {
                String in = scanner.nextLine();
                String[] split = in.split("~");
                //The actual command being read.
                String command = split[0];
                switch (command) {
                    case "HINT":
                        int[] result;
                        if (difficulty == 1) {
                            result = (new NaiveStrategy()).determineMove(board, this.getBall());
                            LOGGER.info("AI suggests move: " + result[0] + " " + result[1]);
                        } else if (difficulty == 2) {
                            result = (new SmartStrategy()).determineMove(board, this.getBall());
                            LOGGER.info("AI suggests move: " + result[0] + " " + result[1]);
                        } else {
                            LOGGER.info("AI has not been activated!");
                        }
                        break;
                    case "MOVE":
                        return checkMove(split);
                    case "HELP":
                        LOGGER.info("""
                                HELP MENU:\s
                                CHANGE to change ai difficulty\s
                                MOVE~<A>~<B>\s
                                HINT  to request a move from the ai\s
                                
                                B := 0 means rotate the top left subboard counter-clockwise\s\040\040
                                B := 1 means rotate the top left subboard clockwise
                                B := 2 means rotate the top right subboard counter-clockwise
                                B := 3 means rotate the top right subboard clockwise
                                B := 4 means rotate the bottom left subboard counter-clockwise
                                B := 5 means rotate the bottom left subboard clockwise
                                B := 6 means rotate the bottom right subboard counter-clockwise
                                B := 7 means rotate the bottom right subboard clockwise
                                """);
                        break;
                    case "CHANGE":
                        if (difficulty == 0) {
                            difficulty = 1;
                            LOGGER.info("Naive AI has been selected!");
                        } else if (difficulty == 1) {
                            difficulty = 2;
                            LOGGER.info("Smart AI has been selected!");
                        } else  if (difficulty == 2) {
                            difficulty = 0;
                            LOGGER.info("AI has been deactivated");
                        }
                        break;
                    case "QUIT":
                        try {
                            throw new ExitProgram("User indicated to exit.");
                        } catch (ExitProgram e) {
                            e.printStackTrace();
                        }
                        break;
                    default:
                        LOGGER.info("Incorrect syntax!");
                        break;
                }
            }
        }
        return move;
    }

    /**
     * This is a helper function to check the input of the user.
     * @param split the array of inputs
     * @return the move is the syntax was correct.
     */
    //@requires split.length == 2;
    //@ensures \result.length == 2;
    public int[] checkMove(String[] split) {
        int[] move = new int[2];
        int par1 = -1, par2 = -1;  // Set defaults for invalid moves
    
        if (split.length > 1) {
            try {
                par1 = Integer.parseInt(split[1]);
            } catch (NumberFormatException e) {
                LOGGER.info("Invalid move!      Syntax:  MOVE~<A>~<B>");
                return move;  // Return early if parsing fails
            }
    
            if (split.length > 2) {
                try {
                    par2 = Integer.parseInt(split[2]);
                } catch (NumberFormatException e) {
                    LOGGER.info("Invalid move!      Syntax:  MOVE~<A>~<B>");
                    return move;
                }
                move[0] = par1;
                move[1] = par2;
                return move;
            }
            LOGGER.info("Invalid move!      Syntax:  MOVE~<A>~<B>");
        }
        return move;  // Return the default or invalid move
    }    
}
