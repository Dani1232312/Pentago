package org.example;

import org.example.controller.Game;
import org.example.model.Balls;
import org.example.model.player.ComputerPlayer;
import org.example.model.player.HumanPlayer;
import org.example.model.player.Player;
import org.example.model.player.computer.SmartStrategy;

import java.util.Scanner;

/**
 * This is the class that starts the application.
 */
public class Pentago {
    private static Game game;


    public static void main(String[] args) {
        game = new Game();
        setUp();
        game.play();
    }

/**
 * A setUp methods that asks the user for input to start a playable game.
 */
    protected static void setUp() {
        printHelloMessage();
        Scanner s = new Scanner(System.in);
        String input = s.nextLine();
        switch (input) {
            case "continue" -> {
                String name;
                System.out.println("Player 1 name:");
                name = s.nextLine();
                Player p1 = new HumanPlayer(name, Balls.WHITE);
                game.setP1(p1);
                System.out.println("Player 2 name:");
                name = s.nextLine();
                Player p2 = new HumanPlayer(name, Balls.BLACK);
                game.setP2(p2);
            }
            case "computer" -> {
                Player p1 = new ComputerPlayer(Balls.WHITE, new SmartStrategy());
                Player p2 = new ComputerPlayer(Balls.BLACK);
                game.setP1(p1);
                game.setP2(p2);
            }
            case "play" -> {
                String name;
                System.out.println("Player 1 name:");
                name = s.nextLine();
                Player p1 = new HumanPlayer(name, Balls.WHITE);
                Player p2 = new ComputerPlayer(Balls.BLACK, new SmartStrategy());
                game.setP1(p1);
                game.setP2(p2);
            }
            default -> System.out.println("Wrong command!");
        }
    }

    public static void printHelloMessage() {
        System.out.println("""
                Welcome to Pentago game!
                Made by Daniel Botnarenco

                Decide how you want to play. For two player type 'continue'.
                For Player v Computer type 'play'
                For Computer v Computer type 'computer'
                """);
    }
}
