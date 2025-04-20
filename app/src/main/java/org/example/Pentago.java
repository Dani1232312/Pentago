package org.example;

import org.example.controller.Game;
import org.example.model.Balls;
import org.example.model.player.ComputerPlayer;
import org.example.model.player.HumanPlayer;
import org.example.model.player.computer.SmartStrategy;

import java.util.Scanner;

public class Pentago {
    private static Game game;

    public static void main(String[] args) {
        game = new Game();
        setUp();
        game.play();
    }

    protected static void setUp() {
        printHelloMessage();
        try (Scanner scanner = new Scanner(System.in)) {
            while (true) {
                String input = scanner.nextLine().trim().toLowerCase();

                switch (input) {
                    case "continue" -> {
                        setupHumanVsHuman(scanner);
                        return;
                    }
                    case "computer" -> {
                        setupComputerVsComputer();
                        return;
                    }
                    case "play" -> {
                        setupHumanVsComputer(scanner);
                        return;
                    }
                    default -> System.out.println("Invalid input. Please type 'continue', 'computer', or 'play'.");
                }
            }
        }
    }

    private static void setupHumanVsHuman(Scanner scanner) {
        System.out.print("Player 1 name: ");
        String name1 = scanner.nextLine();
        System.out.print("Player 2 name: ");
        String name2 = scanner.nextLine();

        game.setP1(new HumanPlayer(name1, Balls.WHITE));
        game.setP2(new HumanPlayer(name2, Balls.BLACK));
    }

    private static void setupHumanVsComputer(Scanner scanner) {
        System.out.print("Player name: ");
        String name = scanner.nextLine();

        game.setP1(new HumanPlayer(name, Balls.WHITE));
        game.setP2(new ComputerPlayer(Balls.BLACK, new SmartStrategy()));
    }

    private static void setupComputerVsComputer() {
        game.setP1(new ComputerPlayer(Balls.WHITE, new SmartStrategy()));
        game.setP2(new ComputerPlayer(Balls.BLACK));
    }

    private static void printHelloMessage() {
        System.out.println("""
                Welcome to Pentago!
                Created by Daniel Botnarenco
                
                Choose a game mode:
                  - For two players, type: continue
                  - For player vs computer, type: play
                  - For computer vs computer, type: computer
                """);
    }
}
