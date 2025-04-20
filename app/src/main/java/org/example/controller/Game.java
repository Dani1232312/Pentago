package org.example.controller;

import org.example.model.Balls;
import org.example.model.Board;
import org.example.model.player.Player;

import java.util.Random;


/**
 * This class contains all the logic of the game.
 */
public class Game {
    private final Board board;
    private Player p1;
    private Player p2;
    private Player currentPlayer;
    private int turn;

    /**
     * This is the constructor for the Game class that initializes a game with a board.
     */
    public Game() {
        board = new Board();
        board.generateBoard();
        Random random = new Random();
        this.turn = random.nextInt();
    }

    /**
     * This method contains the logic of the game.
     */
    public void play() {
        System.out.println();
        int[] move;
        System.out.println(board.toString());
        while (!endGame()) {
            switchPlayers();
            //tell the player is his turn
            System.out.println(currentPlayer.getName() + " makes a move!");
            //get a move from the player
            move = currentPlayer.getMove(board);
            // check if the move is correct
            if (checkMove(move)) {
                makeMove(move);
                System.out.println(board);
            } else {
                System.out.println("Invalid move! Please make another move");
            }
        }
        System.out.println("The game has ended.");
        if (determineWinner() == null) {
            System.out.println("Game ended in a draw!");
        } else {
            Player winner = determineWinner();
            System.out.println(winner.getName() + " is the winner!");
        }
    }

    /**
     * This method checks if the move is valid and will return true or false respectively.
     * @param move an array of move "MOVE~<nr>~<nr>".
     * @return true or false
     */
    //@ ensures \result == true || \result == false;
    //@ requires move.length == 2;
    //@ requires move[0] >= 0 && move[0] < 36;
    //@ requires move[1] >= 0 && move[1] < 9;
    public boolean checkMove(int[] move) {
        int row = move[0] / board.size;
        int col = move[0] % board.size;
        return board.getBall(row, col).equals(Balls.EMPTY) && move[1] >= 0 && move[1] <= 7;
    }

    /**
     * This method calls the appropriate functions to make a move.
     * @param move an array of moves.
     */
    //@ ensures \old(turn) == turn + 1;
    //@ ensures board.getBall(move[0] / board.size, move[0] % board.size)== currentPlayer.getBall();
    //@ requires move.length == 2;
    //@ requires move[0] >= 0 && move[0] < 36;
    //@ requires move[1] >= 0 && move[1] < 9;
    /*@ pure */
    public void makeMove(int[] move) {
        board.move(move[0], currentPlayer.getBall());
        board.rotate(move[1]);
        turn++;
    }

    /**
     * This method check if the game has finished.
     * @return true if the game has finished, false otherwise.
     */
    //@ ensures \result == true || \result == false;
    public boolean endGame() {
        return board.boardIsFull() || board.fiveInARow();
    }

    /**
     * This method return the player which has won or null if both have won.
     * @return null or a player object
     */
    //@ ensures \result == null || \typeof(\result) == currentPlayer.getClass();
    public Player determineWinner() {
        if (board.isWinner(p1.getBall()) && board.isWinner(p2.getBall())) {
            return null;
        } else if (board.isWinner(p1.getBall())) {
            return p1;
        } else if (board.isWinner(p2.getBall())) {
            return p2;
        }
        return null;
    }

    /**
     * This method switches the current player based on the turn number.
     */
    //@ensures \old(currentPlayer) != currentPlayer;
    public void switchPlayers() {
        if (turn % 2 == 0) {
            currentPlayer = p1;
        } else {
            currentPlayer = p2;
        }
    }

    //Setters and getters

    public Board getBoard() {
        return this.board;
    }
    public Player getP1() {
        return p1;
    }
    public Player getP2() {
        return p2;
    }
    public void setP1(Player player) {
        this.p1 = player;
    }
    public void setP2(Player player) {
        this.p2 = player;
    }
    public void setCurrentPlayer(Player player) {
        this.currentPlayer = player;
    }
}
