package org.example;

import org.example.controller.Game;
import org.example.model.Balls;
import org.example.model.Board;
import org.example.model.player.ComputerPlayer;
import org.example.model.player.HumanPlayer;
import org.example.model.player.Player;
import org.example.model.player.computer.NaiveStrategy;
import org.example.model.player.computer.SmartStrategy;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * This class checks if the methods inside the game class are being correctly used.
 * The difference between the Game and Board test is how they access
 * @author Daniel Botnarenco
 */
public class GameTest {
    Game game;
    Player p1;
    Player p2;

    @BeforeEach
    void setUp() {
        game = new Game();
        p1 = new HumanPlayer("Daniel", Balls.WHITE);
        p2 = new HumanPlayer("RandomName", Balls.BLACK);
        game.setP1(p1);
        game.setP2(p2);
    }

    /**
     * This test counts if the winner is returned accordingly to the game logic.
     * If there is no winner the determineWinner() method will return null.
     */
    @Test
    void testCount5() {

        game.setCurrentPlayer(p2);

        game.getBoard().generateBoard();
        //Check if after a new board the winner is not the same by any chance.
        assertNull(game.determineWinner());

        game.getBoard().setBoard("-0~-1~-1~-1~-1~-1" +
                                "~-1~-0~-1~-1~-1~-1" +
                                "~-1~-1~-0~-1~-1~-1" +
                                "~-1~-1~-1~-0~-1~-1" +
                                "~-1~-1~-1~-1~-0~-1" +
                                "~-1~-1~-1~-1~-1~-1");
        assertEquals(game.getP2().getName(), game.determineWinner().getName());

        game.getBoard().setBoard("-0~-1~-1~-1~-1~-1" +
                                "~-0~-1~-1~-1~-1~-1" +
                                "~-0~-1~-1~-1~-1~-1" +
                                "~-0~-1~-1~-1~-1~-1" +
                                "~-0~-1~-1~-1~-1~-1" +
                                "~-1~-1~-1~-1~-1~-1");
        assertEquals(game.getP2().getName(), game.determineWinner().getName());

        game.getBoard().setBoard("-1~-1~-1~-1~-1~-0" +
                                "~-1~-1~-1~-1~-0~-1" +
                                "~-1~-1~-1~-0~-1~-1" +
                                "~-1~-1~-0~-1~-1~-1" +
                                "~-1~-0~-1~-1~-1~-1" +
                                "~-1~-1~-1~-1~-1~-1");
        assertEquals(game.getP2().getName(), game.determineWinner().getName());

        game.getBoard().setBoard("-1~-1~-1~-1~-1~-1" +
                                "~-1~-1~-1~-1~-1~-1" +
                                "~-1~-1~-1~-1~-1~-1" +
                                "~-0~-0~-0~-0~-0~-1" +
                                "~-1~-1~-1~-1~-1~-1" +
                                "~-1~-1~-1~-1~-1~-1");
        assertEquals(game.getP2().getName(), game.determineWinner().getName());

        game.getBoard().setBoard("-0~-1~-1~-1~-1~-1" +
                                "~-0~-1~-1~-1~-1~-1" +
                                "~-0~-1~-1~-1~-1~-1" +
                                "~-0~-1~-1~-1~-1~-1" +
                                "~-1~-1~-1~-1~-1~-1" +
                                "~-1~-1~-1~-1~-1~-1");
        assertNull(game.determineWinner());

        //Test with different coloured marbles
        game.getBoard().setBoard("-0~-1~-1~-1~-1~-1" +
                                "~-1~-0~-1~-1~-1~-1" +
                                "~-1~-1~-0~-1~-1~-1" +
                                "~-1~-1~-1~-0~-1~-1" +
                                "~-1~-1~-1~-1~-3~-1" +
                                "~-1~-1~-1~-1~-1~-1");
        assertNull(game.determineWinner());
    }

    /**
     * This tests uses the board's ability to rotate a specific subboard.
     * It then is compared to the actual expected answer of the rotation.
     */
    @Test
    void testRotate() {
        //create a second board to test on the object
        Board board = new Board();
        //for quadrant 1
        game.getBoard().setBoard("-0~-1~-1~-1~-1~-1" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-1~-0~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1");
        game.getBoard().rotate(1);
        board.setBoard("-1~-1~-0~-1~-1~-1" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-0~-1~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1");
        assertEquals(board.toString(), game.getBoard().toString());
        //for quadrant 2
        game.getBoard().generateBoard();
        game.getBoard().setBoard("-1~-1~-1~-0~-1~-1" +
                "~-1~-1~-1~-1~-0~-0" +
                "~-1~-1~-1~-1~-0~-1" +
                "~-1~-1~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1");
        game.getBoard().rotate(2);
        board.setBoard("-1~-1~-1~-1~-0~-1" +
                "~-1~-1~-1~-1~-0~-0" +
                "~-1~-1~-1~-0~-1~-1" +
                "~-1~-1~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1");
        assertEquals(board.toString(), game.getBoard().toString());
        //for quadrant 3
        game.getBoard().generateBoard();
        game.getBoard().setBoard("-1~-1~-1~-1~-1~-1" +
                "~-0~-1~-1~-0~-0~-0" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-0~-1~-1~-1~-0" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-0~-1~-1~-1~-1");
        game.getBoard().rotate(4);
        board.setBoard("-1~-1~-1~-1~-1~-1" +
                "~-0~-1~-1~-0~-0~-0" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-0" +
                "~-0~-0~-0~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1");
        assertEquals(board.toString(), game.getBoard().toString());
        //for quadrant 4
        game.getBoard().generateBoard();
        game.getBoard().setBoard("-1~-1~-1~-1~-1~-1" +
                "~-0~-1~-1~-0~-0~-0" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-0~-1~-1~-1~-0" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-0~-1~-1~-1~-1");
        game.getBoard().rotate(6);
        board.setBoard("-1~-1~-1~-1~-1~-1" +
                "~-0~-1~-1~-0~-0~-0" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-0~-1~-0~-1~-1" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-0~-1~-1~-1~-1");
        assertEquals(board.toString(), game.getBoard().toString());
    }

    /**
     * This test weather after a move the correct Balls have been places at the right spot.
     */
    @Test
    void testMove() {
        p1 = new HumanPlayer("Daniel", Balls.WHITE);
        p2 = new HumanPlayer("RandomName", Balls.BLACK);
        game.setP1(p1);
        game.setP2(p2);
        game.setCurrentPlayer(p2);
        game.getBoard().generateBoard();

        game.getBoard().move(0, p2.getBall());
        assertEquals(game.getBoard().getBall(0, 0), game.getP2().getBall());

        game.setCurrentPlayer(p1);
        game.getBoard().move(28, p1.getBall());
        assertEquals(game.getBoard().getBall(4, 4), game.getP1().getBall());
    }

        // Testing with incomplete winning patterns (4 balls instead of 5)
        @Test
        public void test_incomplete_winning_patterns() {
            Game game = new Game();
            Player p1 = new HumanPlayer("Player1", Balls.WHITE);
            Player p2 = new HumanPlayer("Player2", Balls.BLACK);
            game.setP1(p1);
            game.setP2(p2);
            game.setCurrentPlayer(p2);
        
            // Test incomplete vertical pattern (only 4 balls)
            game.getBoard().setBoard("-0~-1~-1~-1~-1~-1" +
                                    "~-0~-1~-1~-1~-1~-1" +
                                    "~-0~-1~-1~-1~-1~-1" +
                                    "~-0~-1~-1~-1~-1~-1" +
                                    "~-1~-1~-1~-1~-1~-1" +
                                    "~-1~-1~-1~-1~-1~-1");
            assertNull(game.determineWinner());
        
            // Test incomplete horizontal pattern (only 4 balls)
            game.getBoard().setBoard("-1~-1~-1~-1~-1~-1" +
                                    "~-1~-1~-1~-1~-1~-1" +
                                    "~-0~-0~-0~-0~-1~-1" +
                                    "~-1~-1~-1~-1~-1~-1" +
                                    "~-1~-1~-1~-1~-1~-1" +
                                    "~-1~-1~-1~-1~-1~-1");
            assertNull(game.determineWinner());
        
            // Test incomplete diagonal pattern (only 4 balls)
            game.getBoard().setBoard("-0~-1~-1~-1~-1~-1" +
                                    "~-1~-0~-1~-1~-1~-1" +
                                    "~-1~-1~-0~-1~-1~-1" +
                                    "~-1~-1~-1~-0~-1~-1" +
                                    "~-1~-1~-1~-1~-1~-1" +
                                    "~-1~-1~-1~-1~-1~-1");
            assertNull(game.determineWinner());
        
            // Test pattern with different colored balls breaking the sequence
            game.getBoard().setBoard("-0~-1~-1~-1~-1~-1" +
                                    "~-1~-0~-1~-1~-1~-1" +
                                    "~-1~-1~-0~-1~-1~-1" +
                                    "~-1~-1~-1~-0~-1~-1" +
                                    "~-1~-1~-1~-1~-3~-1" +
                                    "~-1~-1~-1~-1~-1~-1");
            assertNull(game.determineWinner());
        }

            // Testing winner determination with different board configurations
    @Test
    public void test_winner_determination_with_different_patterns() {
        Game game = new Game();
        Player p1 = new HumanPlayer("Player1", Balls.WHITE);
        Player p2 = new HumanPlayer("Player2", Balls.BLACK);
        game.setP1(p1);
        game.setP2(p2);
        game.setCurrentPlayer(p2);
    
        // Test horizontal winning pattern
        game.getBoard().setBoard("-1~-1~-1~-1~-1~-1" +
                                "~-1~-1~-1~-1~-1~-1" +
                                "~-0~-0~-0~-0~-0~-1" +
                                "~-1~-1~-1~-1~-1~-1" +
                                "~-1~-1~-1~-1~-1~-1" +
                                "~-1~-1~-1~-1~-1~-1");
        assertEquals(p2.getName(), game.determineWinner().getName());
    
        // Test vertical winning pattern
        game.getBoard().setBoard("-0~-1~-1~-1~-1~-1" +
                                "~-0~-1~-1~-1~-1~-1" +
                                "~-0~-1~-1~-1~-1~-1" +
                                "~-0~-1~-1~-1~-1~-1" +
                                "~-0~-1~-1~-1~-1~-1" +
                                "~-1~-1~-1~-1~-1~-1");
        assertEquals(p2.getName(), game.determineWinner().getName());
    
        // Test diagonal winning pattern (top-left to bottom-right)
        game.getBoard().setBoard("-0~-1~-1~-1~-1~-1" +
                                "~-1~-0~-1~-1~-1~-1" +
                                "~-1~-1~-0~-1~-1~-1" +
                                "~-1~-1~-1~-0~-1~-1" +
                                "~-1~-1~-1~-1~-0~-1" +
                                "~-1~-1~-1~-1~-1~-1");
        assertEquals(p2.getName(), game.determineWinner().getName());
    
        // Test diagonal winning pattern (top-right to bottom-left)
        game.getBoard().setBoard("-1~-1~-1~-1~-1~-0" +
                                "~-1~-1~-1~-1~-0~-1" +
                                "~-1~-1~-1~-0~-1~-1" +
                                "~-1~-1~-0~-1~-1~-1" +
                                "~-1~-0~-1~-1~-1~-1" +
                                "~-1~-1~-1~-1~-1~-1");
        assertEquals(p2.getName(), game.determineWinner().getName());
    
        // Test no winner
        game.getBoard().generateBoard();
        assertNull(game.determineWinner());
    }

}
