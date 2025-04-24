package org.example.controller;

import org.example.model.Balls;
import org.example.model.Board;
import org.example.model.player.Player;

import java.util.Random;

public class Game {
    private final Board board;
    private Player p1;
    private Player p2;
    private Player currentPlayer;
    private int turn;

    public Game() {
        board = new Board();
        board.generateBoard();
        this.turn = new Random().nextInt(2); // 0 or 1
    }

    public void play() {
        System.out.println("\nGame started!");
        System.out.println(board);

        while (!isGameOver()) {
            switchPlayers();
            System.out.println(currentPlayer.getName() + "'s turn.");
            int[] move = currentPlayer.getMove(board);

            if (isValidMove(move)) {
                makeMove(move);
                System.out.println(board);
            } else {
                System.out.println("Invalid move! Try again.");
            }
        }

        System.out.println("Game over!");
        Player winner = determineWinner();
        if (winner == null) {
            System.out.println("It's a draw!");
        } else {
            System.out.println(winner.getName() + " wins the game!");
        }
    }

    private boolean isValidMove(int[] move) {
        int row = move[0] / Board.SIZE;
        int col = move[0] % Board.SIZE;
        return board.getBall(row, col).equals(Balls.EMPTY) && move[1] >= 0 && move[1] <= 7;
    }

    private void makeMove(int[] move) {
        board.move(move[0], currentPlayer.getBall());
        board.rotate(move[1]);
        turn++;
    }

    private boolean isGameOver() {
        return board.boardIsFull() || board.fiveInARow();
    }

    public Player determineWinner() {
        boolean p1Won = board.isWinner(p1.getBall());
        boolean p2Won = board.isWinner(p2.getBall());

        if (p1Won && p2Won) return null;
        if (p1Won) return p1;
        if (p2Won) return p2;
        return null;
    }

    public void switchPlayers() {
        currentPlayer = (turn % 2 == 0) ? p1 : p2;
    }

    // Getters and setters
    public Board getBoard() {
        return board;
    }

    public Player getP1() {
        return p1;
    }

    public Player getP2() {
        return p2;
    }

    public void setP1(Player p1) {
        this.p1 = p1;
    }

    public void setP2(Player p2) {
        this.p2 = p2;
    }

    public void setCurrentPlayer(Player player) {
        this.currentPlayer = player;
    }
}
