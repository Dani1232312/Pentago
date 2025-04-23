package org.example;

import org.example.model.Balls;
import org.example.model.Board;
import org.example.model.ProtocolMessages;
import org.example.model.player.computer.SmartStrategy;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.net.SocketException;

import static org.junit.jupiter.api.Assertions.assertEquals;

@Disabled("Skipping all tests in ClientTest due to known issues")
/**
 * This test class checks if a invalid message on the server does give an error and lets an AI
 * player, play a full game on the reference server.
 */
public class ClientTest {
    private PrintWriter out;
    private BufferedReader in;
    private Board board;
    private int turn;
    private final String name = "Daniel's TEST Client";
    private boolean check = false;
    private Socket socket;

    @BeforeEach
    void setUp() {
        try {
            check = false;
            //address of the reference server
            InetAddress address;
            address = InetAddress.getByName("130.89.253.64");
            //ip of the server
            int port = 55555;
            socket = new Socket(address, port);
            //how we will write to the server
            out = new PrintWriter(socket.getOutputStream());
            //how we wil read from the server
            in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            board = new Board();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Test if the hello message is read correctly.
     */
    @Test
    void testWrongMessage() {
        String message;
        out.println(ProtocolMessages.HELLO + ProtocolMessages.DELIMITER + name);
        out.flush();
        try {
            message = in.readLine();
            System.out.println(message);
        } catch (IOException e) {
            e.printStackTrace();
        }
        out.println(ProtocolMessages.HELLO + ProtocolMessages.DELIMITER + name);
        out.flush();
        try {
            message = in.readLine();
            assertEquals("ERROR~Unexpected HELLO, current state is LOGIN", message);
        } catch (IOException e) {
            e.printStackTrace();
        }
        try {
            socket.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * This method starts a game of pentago on the reference server and uses the AI to make moves.
     * This method checks most of the inputs from the server so no need for separate test cases
     * for login,hello etc.
     * This method might not work as intended but if it works without crashing it's a good test.
     */
    @Test
    void testRandomPlay() throws IOException {
        String message;
        out.println(ProtocolMessages.HELLO + ProtocolMessages.DELIMITER + name);
        out.flush();
        try {
            message = in.readLine();
            System.out.println(message);
        } catch (IOException e) {
            e.printStackTrace();
        }
        out.println(ProtocolMessages.LOGIN + ProtocolMessages.DELIMITER + name);
        out.flush();
        try {
            message = in.readLine();
            //check if after hello LOGIN is received.
            assertEquals(ProtocolMessages.LOGIN, message);
        } catch (IOException e) {
            e.printStackTrace();
        }

        out.println(ProtocolMessages.QUEUE);
        out.flush();

        message = in.readLine();

        //While reading from the server we will handle the commands received.
        while (message != null) {
            String[] split = message.split("~");
            switch (split[0]) {
                case ProtocolMessages.NEWGAME -> {
                    turn = 1;
                    int c = -1;
                    for (int i = 1; i < split.length; i++) {
                        if (split[i].equals(name)) {
                            c = i;
                        }
                    }
                    board.generateBoard();
                    if (c == 1) {
                        turn = 0;
                        //the AI will play for us.
                        int[] move = (new SmartStrategy()).determineMove(board, Balls.BLACK);
                        out.println(ProtocolMessages.MOVE + ProtocolMessages.DELIMITER + move[0]
                                + ProtocolMessages.DELIMITER + move[1]);
                        out.flush();
                    }
                    assertEquals(ProtocolMessages.NEWGAME, split[0]);
                }
                case ProtocolMessages.MOVE -> {
                    //check when it's my turn
                    if (turn % 2 == 1) {
                        board.move(Integer.parseInt(split[1]), Balls.BLACK);
                        board.rotate(Integer.parseInt(split[2]));
                        //the AI will play for us.
                        int[] move = (new SmartStrategy()).determineMove(board, Balls.BLACK);
                        out.println(ProtocolMessages.MOVE + ProtocolMessages.DELIMITER + move[0]
                                + ProtocolMessages.DELIMITER + move[1]);
                        out.flush();
                    } else {
                        board.move(Integer.parseInt(split[1]), Balls.WHITE);
                        board.rotate(Integer.parseInt(split[2]));
                    }
                    turn++;
                }
                case ProtocolMessages.GAMEOVER -> {
                    //was able to finish the game
                    assertEquals(ProtocolMessages.GAMEOVER, split[0]);
                    out.write(ProtocolMessages.LIST);
                    out.flush();
                    check = true;
                }
            }
            System.out.println(message);
            message = in.readLine();
            out.flush();
            if (check) {
                try {
                    socket.close();
                } catch (SocketException e) {
                    System.out.println("Finished testing");
                }
                break;
            }
        }
    }
}
