package model.player;

import exceptions.ExitProgram;
import model.Balls;

import java.util.Scanner;

import model.Board;
import model.player.computer.NaiveStrategy;
import model.player.computer.SmartStrategy;


/**
 * A type of player class.
 */
public class HumanPlayer extends Player {
    private int difficulty = 0;

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
        System.out.println("It's your turn to make a move!");
        System.out.println("MOVE~<A>~<B>");
        Scanner scanner = new Scanner(System.in);

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
                        System.out.println("AI suggests move: " + result[0] + " " + result[1]);
                    } else if (difficulty == 2) {
                        result = (new SmartStrategy()).determineMove(board, this.getBall());
                        System.out.println("AI suggests move: " + result[0] + " " + result[1]);
                    } else {
                        System.out.println("AI has not been activated!");
                    }
                    break;
                case "MOVE":
                    return checkMove(split);
                case "HELP":
                    System.out.println("""
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
                        System.out.println("Naive AI has been selected!");
                    } else if (difficulty == 1) {
                        difficulty = 2;
                        System.out.println("Smart AI has been selected!");
                    } else  if (difficulty == 2) {
                        difficulty = 0;
                        System.out.println("AI has been deactivated");
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
                    System.out.println("Incorrect syntax!");
                    break;
            }
        }
        scanner.close();
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
        int par1;
        int par2;
        if (split.length > 1) {
            par1 = Integer.parseInt(split[1]);
            if (split.length > 2) {
                par2 = Integer.parseInt(split[2]);
                move = new int[2];
                move[0] = par1;
                move[1] = par2;
                return move;
            }
            System.out.println("Invalid move!      Syntax:  MOVE~<A>~<B>");
        }
        return move;
    }
}
