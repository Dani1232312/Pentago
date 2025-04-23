package org.example;

import org.example.controller.Client;
import org.example.exceptions.ExitProgram;
import org.example.exceptions.ServerUnavailableException;
import org.example.model.Board;
import org.example.view.ClientView;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;

/**
 * This is the class that initializes a connection to a server and
 * starts listening on it.
 */
public class ClientTUI {
    private String name;
    private final ClientView view;
    private Socket serverSock;
    private BufferedReader in;
    private BufferedWriter out;
    private boolean ai = false;
    private boolean turn = false;
    private Board board;
    private boolean inGame = false;

    /**
     * The constructor of the class.
     * It creates a new view and board.
     */
    public ClientTUI() {
        view = new ClientView(this);
        board = new Board();
        board.generateBoard();
    }

    /**
     * This method initializes the client to play an online game.
     * @param args standard
     */
    public static void main(String[] args) {
        (new ClientTUI()).start();
    }

    /**
     * This method starts a connection with a server and a view.
     */
    public void start() {
        try {
            //join a server
            createConnection();
            //start the view
            view.start();
        } catch (ServerUnavailableException | ExitProgram | UnknownHostException e) {
            closeConnection();
        }
    }

    /**
     * This method creates a connection to a specific IP and port. If one of these is not correct
     * the program will continue to run until a valid ip and port are given.
     * @throws ExitProgram if the user wants to exit
     * @throws UnknownHostException if the server address is not correct
     */
    public void createConnection() throws ExitProgram, UnknownHostException {
        clearConnection();
        while (serverSock == null) {
            //InetAddress ip = InetAddress.getByName("stekelenburg.me");
            InetAddress address = view.getIp();
            int port = view.getPort();

            // try to open a Socket to the server
            try {
                view.showMessage("Attempting to connect to " + address + ":" + port + "...");
                serverSock = new Socket(address, port);
                in = new BufferedReader(new InputStreamReader(serverSock.getInputStream()));
                out = new BufferedWriter(new OutputStreamWriter(serverSock.getOutputStream()));
                view.showMessage("Connection successful.");

                // Initialize the listener, that will take all the messages coming from the
                // server and forward them to the view
                Client listener = new Client(serverSock, this);
                (new Thread(listener)).start();
            } catch (IOException e) {
                view.showMessage("ERROR: could not create a socket on " +
                        address.getHostAddress() + " and port " + port + ".");

                // Do you want to try again?
                if (!view.getBoolean("Do you want to try again?")) {
                    throw new ExitProgram("User indicated to exit.");
                } else {
                    start();
                }
            }
        }
    }

    /**
     * This method clears the connection.
     * Resets the socket and the streams.
     */
    //@ ensures serverSock == null;
    //@ ensures in == null;
    //@ ensures out == null;
    void clearConnection() {
        serverSock = null;
        in = null;
        out = null;
    }

    /**
     * Closes the connection by closing the streams, as well as the socket.
     */
    //@ ensures serverSock == null;
    //@ ensures in == null;
    //@ ensures out == null;
    public void closeConnection() {
        System.out.println("Closing the connection...");
        try {
            if (in != null) {
                in.close();
                out.close();
                serverSock.close();
                view.showMessage("");
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * This method sends a message from the client to the server.
     * @param message a message to be sent
     * @throws ServerUnavailableException an error increase the server is unavailable.
     */
    //@ requires message != null;
    public synchronized void sendMessage(String message) throws ServerUnavailableException {
        if (out != null) {
            try {
                out.write(message);
                out.newLine();
                out.flush();
            } catch (IOException e) {
                System.out.println(e.getMessage());
                throw new ServerUnavailableException("Could not write " + "to server.");
            }
        } else {
            throw new ServerUnavailableException("Could not write " + "to server.");
        }
    }

    //Setters and getters

    public synchronized void setAi(boolean b) {
        ai = b;
    }

    public synchronized boolean getAi() {
        return ai;
    }

    public synchronized ClientView getView() {
        return this.view;
    }

    public synchronized void setName(String name) {
        this.name = name;
    }

    public synchronized String getName() {
        return this.name;
    }

    public synchronized Board getBoard() {
        return board;
    }

    public synchronized void setBoard(Board board) {
        this.board = board;
    }

    public void setTurn(boolean b) {
        this.turn = b;
    }

    public boolean getTurn() {
        return this.turn;
    }

    public synchronized boolean getInGame() {
        return this.inGame; }

    public void setInGame(boolean b) {
        this.inGame = b;
    }

}
