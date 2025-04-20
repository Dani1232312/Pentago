package org.example.controller;

import org.example.model.ProtocolMessages;

import java.io.BufferedReader;
import java.io.PrintWriter;
import java.io.Reader;
import java.io.Writer;

/**
 * A class that implements the Runnable class. And only
 * listens for the PING command from the server.
 */
public class PingPong implements Runnable{
    private boolean ping = true;
    BufferedReader in;
    PrintWriter printWriter;
    Client client;

    /**
     * The constructor to create the PingPong thread.
     * @param input from where to read data
     * @param output where to write data
     * @param client the client from which to send the data
     */
    public PingPong(Reader input, Writer output, Client client) {
        this.client = client;
         in = new BufferedReader(input);
         printWriter = new PrintWriter(output, true);
    }

    /**
     * This thread run method waits for a state change from the client to send a ping back to the server.
     */
    @Override
    public void run() {
        while (!ping) {
            try {
                wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        client.sendMessage(ProtocolMessages.PONG);
    }

    public synchronized void setPing(boolean b) {
        ping = b;
    }
}
