package controller;

import exceptions.ExitProgram;
import model.Balls;
import model.ProtocolMessages;
import model.player.computer.SmartStrategy;
import run.ClientTUI;

import java.io.*;
import java.net.Socket;
import java.net.SocketException;

/**
 * This class communicates with the server on a separate thread.
 */
public class Client implements Runnable {
    private PrintWriter out;
    private BufferedReader in;
    private Socket socket;
    private int turn;
    private ClientTUI client;
    private final Balls ball = Balls.BLACK;
    private PingPong pingPong ;


    /**
     * This is the constructor for the client that requires a socket to read/write to.
     * @param socket the socket to which it will communicate.
     */
    public Client(Socket socket, ClientTUI client) {
        try {
            this.client = client;
            this.socket = socket;
            //how we will write to the server
            out = new PrintWriter(socket.getOutputStream());
            //how we wil read from the server
            in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
        } catch (IOException e) {
            client.getView().showMessage("IOException occurred!");
            System.exit(1);
        }
    }

    @Override
    public void run() {
        String message;
        try {
            pingPong = new PingPong(in, out, this);
            new Thread(pingPong).start();
            message = in.readLine();
            //While reading from the server we will handle the commands received.
            while (message != null) {
                client.getView().showMessage(handleCommand(message));
                message = in.readLine();
            }
            //if server stops running we will close the streams and the socket
            try {
                in.close();
                out.close();
                socket.close();
            } catch (IOException e) {
                client.getView().showMessage("The server has disconnected.");
                client.closeConnection();
            }
        } catch (SocketException e) {
            client.getView().showMessage("The server has disconnected.");
            client.closeConnection();
        } catch (IOException e) {
            client.getView().showMessage("The server has disconnected.");
            client.closeConnection();
        }
    }

    /**
     * This method looks at the message received by the client from the server.
     * Each message has a specific reply as shown in the protocol.
     * @param message a message to handle
     * @return a text to be shown to the user.
     */
    //@ ensures \result >= 0;
    //@ requires message != null;
    private synchronized String handleCommand(String message) {
        String[] split = message.split("~");
        //check the message
        switch (split[0]) {
            case ProtocolMessages.PING -> pingPong.setPing(true);
            case ProtocolMessages.NEWGAME -> doNewGame(split);
            case ProtocolMessages.MOVE -> {
                //check when it's my turn
                if (turn % 2 == 1) {
                    client.setTurn(true);
                    client.getBoard().move(Integer.parseInt(split[1]), Balls.BLACK);
                    client.getBoard().rotate(Integer.parseInt(split[2]));
                    //check if AI is activated
                    if (client.getAi()) {
                        int[] move = (new SmartStrategy()).determineMove(client.getBoard(), Balls.BLACK);
                        sendMessage(ProtocolMessages.MOVE + ProtocolMessages.DELIMITER + move[0] + ProtocolMessages.DELIMITER + move[1]);
                    }
                    client.getView().showMessage("It's your turn to make a move!");
                } else {
                    client.setTurn(false);
                    client.getBoard().move(Integer.parseInt(split[1]), Balls.WHITE);
                    client.getBoard().rotate(Integer.parseInt(split[2]));
                }
                client.getView().showMessage(client.getBoard().toString());
                turn++;
                return "LAST MOVE:" + message;
            }
            case ProtocolMessages.GAMEOVER -> {
                client.getView().printHelpMenu();
                client.setInGame(false);
                if (client.getAi()) {
                    sendMessage(ProtocolMessages.QUEUE);
                }
            }
            case ProtocolMessages.QUIT -> {
                try {
                    throw new ExitProgram("Server indicated to exit.");
                } catch (ExitProgram e) {
                    client.getView().showMessage("You exited the program!");
                    System.exit(1);
                }
            }
            case ProtocolMessages.LOGIN -> new Thread(pingPong).start();
        }
        return message;
    }

    /**
     * This method send a message from the client to the server.
     * @param message a message to be sent.
     */
    //@ requires message != null;
    public void sendMessage(String message) {
        out.println(message);
        out.flush();
    }

    /**
     * This is a helper function about the new game protocol message.
     */
    //@ requires move.length == 2;
    public void doNewGame(String[] split) {
        boolean newGame = true;
        client.setInGame(newGame);
        turn = 1;
        int c = -1;
        for (int i = 1; i < split.length; i++) {
            if (split[i].equals(client.getName())) {
                c = i;
            }
        }
        client.getBoard().generateBoard();
        if (c == 1) {
            turn = 0;
            //if AI is turned on a move will be made by him
            if (client.getAi()) {
                int[] move = (new SmartStrategy()).determineMove(client.getBoard(), ball);
                sendMessage(ProtocolMessages.MOVE + ProtocolMessages.DELIMITER
                        + move[0] + ProtocolMessages.DELIMITER + move[1]);
            }
            //determine a move
            client.getView().showMessage("You move first!");
        }
        client.getView().showMessage(client.getBoard().toString());
    }

}
