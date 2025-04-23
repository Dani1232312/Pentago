package org.example.view;

import org.example.exceptions.ServerUnavailableException;
import org.example.exceptions.TooFewArguments;
import org.example.model.Balls;
import org.example.model.ProtocolMessages;
import org.example.model.player.computer.NaiveStrategy;
import org.example.model.player.computer.SmartStrategy;
import org.example.ClientTUI;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.InputMismatchException;
import java.util.Scanner;

public class ClientView {
    private int difficulty = 0;
    private boolean inQueue = false;
    private boolean server = true;
    private final Scanner s = new Scanner(System.in);

    private final ClientTUI client;

    public ClientView(ClientTUI clientTUI) {
        this.client = clientTUI;
    }

    /**
     * Starts a new client view. Take input from the user and sent it to handleuserinput().
     *
     * @throws ServerUnavailableException if IO errors occur.
     */
    public synchronized void start() throws ServerUnavailableException {
        printHelpMenu();
        s.nextLine();
        while (server) {
            try {
                Thread.sleep(500);
            } catch (InterruptedException e) {
                showMessage("Error occurred!");
                System.exit(1);
            }
            showMessage("Enter command: ");
            try {
                handleuserinput(getLine());
            } catch (TooFewArguments e) {
                showMessage(e.getMessage());
            }
        }
    }

    /**
     * This method looks at the input of the Client and parses it to be sent to the server following the
     * protocol.
     * @param input a string that is being read from the client.
     * @throws ServerUnavailableException in case the server fails it will throw an error.
     */
    public void handleuserinput(String input) throws ServerUnavailableException, TooFewArguments {
        String[] split = input.split("~");
        switch (split[0]) {
            case ProtocolMessages.HELLO:
                if (split.length == 2) {
                    client.sendMessage(ProtocolMessages.HELLO + ProtocolMessages.DELIMITER + split[1]);
                } else {
                    throw new TooFewArguments("The command does not have the right syntax!");
                }
                break;
            case ProtocolMessages.PING:
                client.sendMessage(ProtocolMessages.PING);
                break;
            case ProtocolMessages.QUIT:
                if (split.length > 1) {
                    throw new TooFewArguments("The command does not have the right syntax!");
                }
                server = false;
                client.sendMessage(ProtocolMessages.QUIT);
                client.closeConnection();
                System.exit(1);
                break;
            case ProtocolMessages.QUEUE:
                if(client.getInGame()) {
                    showMessage("Not allowed to QUEUE at this time");
                } else {
                    if (!inQueue) {
                        inQueue = true;
                        showMessage("You entered the queue!");
                    } else {
                        inQueue = false;
                        showMessage("You have left the queue!");
                    }
                    client.sendMessage(ProtocolMessages.QUEUE);
                }
                break;
            case ProtocolMessages.MOVE:
                if (client.getTurn()) {
                    client.sendMessage(ProtocolMessages.MOVE + ProtocolMessages.DELIMITER + split[1] + ProtocolMessages.DELIMITER + split[2]);
                } else {
                    showMessage("You are not allowed to move yet!");
                }
                break;
            case ProtocolMessages.LIST:
                client.sendMessage(ProtocolMessages.LIST);
                break;
            case ProtocolMessages.HELP:
                printHelpMenu();
                break;
            case ProtocolMessages.LOGIN:
                if (split.length > 1) {
                    client.setName(split[1]);
                    client.sendMessage(ProtocolMessages.LOGIN + ProtocolMessages.DELIMITER + split[1]);
                } else {
                    showMessage("Invalid Syntax");
                }
                break;
            case "AI":
                if (client.getAi()) {
                    client.setAi(false);
                    showMessage("AI has been deactivated!");
                } else {
                    client.setAi(true);
                    showMessage("AI has been activated!");
                }
                break;
            case "HINT":
                int[] result;
                if (difficulty == 1) {
                    result = (new NaiveStrategy()).determineMove(client.getBoard(), Balls.BLACK);
                    showMessage("AI suggests move: " + result[0] + " " + result[1]);
                } else if (difficulty == 2) {
                    result = (new SmartStrategy()).determineMove(client.getBoard(), Balls.BLACK);
                    showMessage("AI suggests move: " + result[0] + " " + result[1]);
                } else {
                    showMessage("AI has not been activated!");
                }
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
            default:
                showMessage("Invalid command please try another one!");
                break;
        }
    }


    /**
     * Reads an entire line from the scanner and returns it.
     * @return next line from scanner
     */
    public String getLine() {
        return s.nextLine();
    }

    /**
     * Reads a port from the scanner and checks if it's valid.
     */
    //@ ensures port>=1 && port <= 65535;
    public int getPort() {
        int i = -1;
        while (i < 0 || i > 65535) {
            try {
                showMessage("Connecting to port: ");
                i = s.nextInt();
            } catch (InputMismatchException e) {
                s.next();
            }
        }
        return i;
    }

    /**
     * Checks if the given string is a valid IP address.
     *
     * @param ip the string representation of the IP.
     * @return true if the string is valid, false otherwise.
     */
    private static boolean validIP(String ip) {
        try {
            if (ip == null || ip.isEmpty()) {
                return false;
            }

            String[] parts = ip.split("\\.");
            if (parts.length != 4) {
                return false;
            }

            for (String s : parts) {
                int i = Integer.parseInt(s);
                if (i < 0 || i > 255) {
                    return false;
                }
            }
            return !ip.endsWith(".");
        } catch (NumberFormatException nfe) {
            return false;
        }
    }

    /**
     * Reads a string from the scanner.
     *
     * @param message question to be printed beforehand
     * @return the string that the user entered.
     */
    private String getString(String message) {
        showMessage(message);
        String string;
        while (!s.hasNext()) {
            s.next();
        }
        string = s.next();
        return string;
    }

    /**
     * Reads a string from the scanner and translates it into an InetAddress.
     */
    //@ ensures \result == true;
    public InetAddress getIp() {
        InetAddress ipp = null;

        String ip = getString("Enter a valid IP Address: ");
        while (!validIP(ip)) {
            ip = getString("The entered IP address is not valid. Please type again: ");
        }
        try {
            ipp = InetAddress.getByName(ip);
        } catch (UnknownHostException e) {
            showMessage("Could not connect to the server!");
        }

        return ipp;
    }

    /**
     * Prints a message on the console.
     *
     * @param s message to be printed.
     */
    public void showMessage(String s) {
        System.out.println(s);
    }

    /**
     * Prints the help menu on the console.
     */
    public void printHelpMenu() {
        System.out.println();
        System.out.println("""
                HELP MENU:\s
                 LIST\s
                 QUEUE\s
                 MOVE~<A>~<B>\s
                 AI                  to activate AI\s
                 CHANGE     to change AI difficulty\s
                 HELP\s
                """);
    }

    public boolean getBoolean(String question) {
        showMessage(question + "(yes/no answer): ");
        String response = s.next();
        return response.equals("yes");
    }
}
