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
import java.util.logging.Logger;

public class ClientView {
    private static final String AI_COMMAND = "AI";
    private static final String QUIT_COMMAND = "QUIT";
    private static final String INVALID_IP_MESSAGE = "Could not connect to the server!";
    private static final String HINT_COMMAND = "HINT";
    private static final String CHANGE_COMMAND = "CHANGE";
    private static final String INVALID_COMMAND_MESSAGE = "Invalid command syntax!";
    private static final String AI_DEACTIVATED_MESSAGE = "AI Deactivated";
    private static final String AI_ACTIVATED_MESSAGE = "AI Activated";
    private static final String AI_CHANGE_MESSAGE = "AI Difficulty Changed";
    private static final String NOT_ALLOWED_TO_MOVE_MESSAGE = "You are not allowed to move at this time";
    private static final int EASY_DIFFICULTY = 1;
    private static final int MEDIUM_DIFFICULTY = 2;
    private static final int NO_AI_DIFFICULTY = 0;
    // Other constants...
    private int difficulty = 0;
    private boolean inQueue = false;
    private boolean server = true;
    private final Scanner s = new Scanner(System.in);
    private static final Logger logger = Logger.getLogger(ClientView.class.getName());

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
                // Handle the error gracefully instead of exiting the VM
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
            case QUIT_COMMAND:
                if (split.length > 1) {
                    throw new TooFewArguments("The command does not have the right syntax!");
                }
                server = false;
                client.sendMessage(ProtocolMessages.QUIT);
                client.closeConnection();
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
                    showMessage(NOT_ALLOWED_TO_MOVE_MESSAGE);
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
            case AI_COMMAND:
                if (client.getAi()) {
                    client.setAi(false);
                    showMessage(AI_DEACTIVATED_MESSAGE);
                } else {
                    client.setAi(true);
                    showMessage(AI_ACTIVATED_MESSAGE);
                }
                break;
            case HINT_COMMAND:  // Use constant here
                int[] result;
                if (difficulty == EASY_DIFFICULTY) {
                    result = (new NaiveStrategy()).determineMove(client.getBoard(), Balls.BLACK);
                    showMessage("AI suggests move: " + result[0] + " " + result[1]);
                } else if (difficulty == MEDIUM_DIFFICULTY) {
                    result = (new SmartStrategy()).determineMove(client.getBoard(), Balls.BLACK);
                    showMessage("AI suggests move: " + result[0] + " " + result[1]);
                } else {
                    showMessage("AI has not been activated!");
                }                
                break;
            case CHANGE_COMMAND:  // Use constant here
                if (difficulty == 0) {
                    difficulty = 1;
                    showMessage(AI_CHANGE_MESSAGE);
                } else if (difficulty == 1) {
                    difficulty = 2;
                    showMessage(AI_CHANGE_MESSAGE);
                } else if (difficulty == 2) {
                    difficulty = 0;
                    showMessage(AI_DEACTIVATED_MESSAGE);
                }
                break;
            default:
                showMessage(INVALID_COMMAND_MESSAGE);  // Use constant here
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
            showMessage(INVALID_IP_MESSAGE);
        }

        return ipp;
    }

    /**
     * Prints a message on the console.
     *
     * @param s message to be printed.
     */
    public void showMessage(String message) {
        logger.info(message); // Use a logger instead of System.out.println
    }

    /**
     * Prints the help menu on the console.
     */
    public void printHelpMenu() {
        showMessage("");
        showMessage("""
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
        return "yes".equals(response);
    }
}
