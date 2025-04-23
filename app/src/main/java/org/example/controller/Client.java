package org.example.controller;

import org.example.ClientTUI;
import org.example.exceptions.ExitProgram;
import org.example.model.Balls;
import org.example.model.ProtocolMessages;
import org.example.model.player.computer.SmartStrategy;

import java.io.*;
import java.net.Socket;
import java.net.SocketException;

/**
 * Handles communication with the server on a separate thread.
 */
public class Client implements Runnable {
    private PrintWriter out;
    private BufferedReader in;
    private Socket socket;
    private int turn;
    private final ClientTUI client;
    private PingPong pingPong;

    public Client(Socket socket, ClientTUI client) {
        this.client = client;
        this.socket = socket;
        try {
            this.out = new PrintWriter(socket.getOutputStream(), true);
            this.in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
        } catch (IOException e) {
            client.getView().showMessage("Connection setup failed: " + e.getMessage());
            System.exit(1);
        }
    }

    @Override
    public void run() {
        try {
            this.pingPong = new PingPong(in, out, this);
            new Thread(pingPong).start();

            String message;
            while ((message = in.readLine()) != null) {
                client.getView().showMessage(handleCommand(message));
            }
        } catch (SocketException e) {
            client.getView().showMessage("Lost connection to the server.");
        } catch (IOException e) {
            client.getView().showMessage("I/O error: " + e.getMessage());
        } finally {
            closeResources();
        }
    }

    private void closeResources() {
        try {
            if (in != null) in.close();
            if (out != null) out.close();
            if (socket != null && !socket.isClosed()) socket.close();
        } catch (IOException e) {
            client.getView().showMessage("Failed to close resources.");
        } finally {
            client.closeConnection();
        }
    }

    private synchronized String handleCommand(String message) {
        String[] parts = message.split(ProtocolMessages.DELIMITER);
        String command = parts[0];

        switch (command) {
            case ProtocolMessages.PING -> pingPong.setPing(true);

            case ProtocolMessages.NEWGAME -> handleNewGame(parts);

            case ProtocolMessages.MOVE -> {
                int position = Integer.parseInt(parts[1]);
                int rotation = Integer.parseInt(parts[2]);

                if (turn % 2 == 1) {
                    client.setTurn(true);
                    client.getBoard().move(position, Balls.BLACK);
                    client.getBoard().rotate(rotation);
                    handleAI();
                } else {
                    client.setTurn(false);
                    client.getBoard().move(position, Balls.WHITE);
                    client.getBoard().rotate(rotation);
                }

                turn++;
                client.getView().showMessage(client.getBoard().toString());
                return "LAST MOVE: " + message;
            }

            case ProtocolMessages.GAMEOVER -> {
                client.setInGame(false);
                client.getView().printHelpMenu();
                if (client.getAi()) sendMessage(ProtocolMessages.QUEUE);
            }

            case ProtocolMessages.QUIT -> {
                try {
                    throw new ExitProgram("Server terminated the game.");
                } catch (ExitProgram e) {
                    client.getView().showMessage("You exited the program!");
                    System.exit(0);
                }
            }

            case ProtocolMessages.LOGIN -> new Thread(pingPong).start();

            default -> client.getView().showMessage("Unknown command received: " + command);
        }

        return message;
    }

    private void handleAI() {
        if (client.getAi()) {
            int[] move = new SmartStrategy().determineMove(client.getBoard(), Balls.BLACK);
            sendMessage(ProtocolMessages.MOVE + ProtocolMessages.DELIMITER +
                        move[0] + ProtocolMessages.DELIMITER + move[1]);
        }
        client.getView().showMessage("It's your turn to make a move!");
    }

    public void sendMessage(String message) {
        out.println(message);
    }

    public void handleNewGame(String[] players) {
        client.setInGame(true);
        turn = 1;
        int myIndex = -1;

        for (int i = 1; i < players.length; i++) {
            if (players[i].equals(client.getName())) {
                myIndex = i;
                break;
            }
        }

        client.getBoard().generateBoard();
        if (myIndex == 1) {
            turn = 0;
            if (client.getAi()) handleAI();
            client.getView().showMessage("You move first!");
        }

        client.getView().showMessage(client.getBoard().toString());
    }
}
