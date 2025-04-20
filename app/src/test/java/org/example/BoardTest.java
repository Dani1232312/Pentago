package org.example;

import org.example.model.Balls;
import org.example.model.Board;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.*;

/**
 * This test class tests the manipulation of the board object.
 */
public class BoardTest {
    Board board;

    @BeforeEach
    void setUp() {
        board = new Board();
        board.generateBoard();
    }

    @Test
    void testGeneration() {
        for (int row = 0; row < board.size; row++) {
            for (int col = 0; col < board.size; col++) {
                if (board.getBall(row, col).equals(Balls.BLACK) ||
                        board.getBall(row, col).equals(Balls.WHITE) ||
                        board.getBall(row, col) == null) {
                    Assertions.fail();
                }
            }
        }
        assertTrue(true);
    }

    /**
     * This test checks weather a move of a ball is set properly.
     */
    @Test
    void testMove() {
        int move = 0;
        // the move to be made
        board.move(move, Balls.BLACK);
        assertEquals(board.getBall(0, 0), Balls.BLACK);
    }

    /**
     * This test check weather there are still empty spaces on the board.
     */
    @Test
    void testFullBoard() {
        board.setBoard("-0~-1~-0~-1~-0~-1" +
                        "~-0~-1~-0~-1~-0~-1" +
                        "~-1~-0~-1~-0~-1~-0" +
                        "~-0~-1~-0~-1~-0~-1" +
                        "~-1~-0~-1~-0~-1~-0" +
                        "~-1~-1~-0~-1~-1~-1");
        assertFalse(board.boardIsFull());

        board.setBoard("1~1~1~1~1~1" +
                        "~1~1~1~1~1~1" +
                        "~1~1~1~1~1~1" +
                        "~1~1~1~1~1~1" +
                        "~1~1~1~1~1~1" +
                        "~1~1~1~1~1~1");
        assertTrue(board.boardIsFull());
    }

    /**
     * This test counts if the winner is returned accordingly to the board.
     * If there is no winner the determineWinner() method will return null.
     */
    @Test
    void testCount5() {
        board.generateBoard();
        //Check if after a new board the winner is not the same by any chance.
        assertFalse(board.fiveInARow());

        //Check different rotations of a line made out of 5 balls.
        board.setBoard("-0~-1~-1~-1~-1~-1" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-1~-0~-1~-1~-1" +
                "~-1~-1~-1~-0~-1~-1" +
                "~-1~-1~-1~-1~-0~-1" +
                "~-1~-1~-1~-1~-1~-1");
        assertTrue(board.fiveInARow());

        board.setBoard("-0~-1~-1~-1~-1~-1" +
                "~-0~-1~-1~-1~-1~-1" +
                "~-0~-1~-1~-1~-1~-1" +
                "~-0~-1~-1~-1~-1~-1" +
                "~-0~-1~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1");
        assertTrue(board.fiveInARow());

        board.setBoard("-1~-1~-1~-1~-1~-0" +
                "~-1~-1~-1~-1~-0~-1" +
                "~-1~-1~-1~-0~-1~-1" +
                "~-1~-1~-0~-1~-1~-1" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1");
        assertTrue(board.fiveInARow());

        board.setBoard("-1~-1~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1" +
                "~-0~-0~-0~-0~-0~-1" +
                "~-1~-1~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1");
        assertTrue(board.fiveInARow());

        board.setBoard("-0~-1~-1~-1~-1~-1" +
                "~-0~-1~-1~-1~-1~-1" +
                "~-0~-1~-1~-1~-1~-1" +
                "~-0~-1~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1" +
                "~-1~-1~-1~-1~-1~-1");
        assertFalse(board.fiveInARow());

        //Test with different coloured marbles
        board.setBoard("-0~-1~-1~-1~-1~-1" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-1~-0~-1~-1~-1" +
                "~-1~-1~-1~-0~-1~-1" +
                "~-1~-1~-1~-1~-3~-1" +
                "~-1~-1~-1~-1~-1~-1");
        assertFalse(board.fiveInARow());
    }

    /**
     * This method tests if getting a specific subboard works as intended.
     */
    @Test
    public void testGetSubboard() {
        Balls[][] subboard = {
                {Balls.BLACK, Balls.WHITE, Balls.EMPTY},
                {Balls.EMPTY, Balls.BLACK, Balls.EMPTY},
                {Balls.EMPTY, Balls.EMPTY, Balls.BLACK},
        };


        board.setBoard("0~1~-1~-1~-1~-1" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-1~-0~-1~-1~-1" +
                "~-1~-1~-1~-0~-1~-1" +
                "~-1~-1~-1~-1~-3~-1" +
                "~-1~-1~-1~-1~-1~-1");

        //1st QUADRANT
        assertEquals(Arrays.deepToString(subboard), Arrays.deepToString(board.getSubBoard(0)));

        subboard = new Balls[][]{
                {Balls.WHITE, Balls.WHITE, Balls.EMPTY},
                {Balls.EMPTY, Balls.EMPTY, Balls.EMPTY},
                {Balls.EMPTY, Balls.EMPTY, Balls.EMPTY},
        };



        board.setBoard("0~1~-1~1~1~-1" +
                    "~-1~-0~-1~-1~-1~-1" +
                    "~-1~-1~-0~-1~-1~-1" +
                    "~-1~-1~-1~-0~-1~-1" +
                    "~-1~-1~-1~-1~-3~-1" +
                    "~-1~-1~-1~-1~-1~-1");

        //2nd QUADRANT
        assertEquals(Arrays.deepToString(subboard), Arrays.deepToString(board.getSubBoard(3)));

        subboard = new Balls[][]{
                {Balls.BLACK, Balls.EMPTY, Balls.EMPTY},
                {Balls.EMPTY, Balls.BLACK, Balls.EMPTY},
                {Balls.EMPTY, Balls.BLACK, Balls.BLACK},
        };

        board.setBoard("0~1~-1~-1~-1~-1" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-1~-0~-1~-1~-1" +
                "~-0~-1~-1~-0~-1~-1" +
                "~-1~0~-1~-1~1~-1" +
                "~-1~0~-0~-1~-1~-1");

        //3rd QUADRANT
        assertEquals(Arrays.deepToString(subboard), Arrays.deepToString(board.getSubBoard(4)));

        subboard = new Balls[][]{
                {Balls.WHITE, Balls.BLACK, Balls.WHITE},
                {Balls.WHITE, Balls.BLACK, Balls.EMPTY},
                {Balls.WHITE, Balls.BLACK, Balls.WHITE},
        };


        board.setBoard("0~1~-1~-1~-1~-1" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-1~-0~-1~-1~-1" +
                "~-1~-1~-1~1~-0~1" +
                "~-1~-1~-1~1~-0~-1" +
                "~-1~-1~-1~1~-0~1");
        //4th QUADRANT
        assertEquals(Arrays.deepToString(subboard), Arrays.deepToString(board.getSubBoard(6)));
    }

    /**
     * This method checks weather setting a subboard works as intended.
     */
    @Test
    public void testSetSubboard() {
        board.setBoard("0~1~-1~-1~-1~-1" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-1~-0~-1~-1~-1" +
                "~1~0~0~1~-0~1" +
                "~-1~1~1~1~-0~-1" +
                "~-1~-1~1~1~-0~1");

        Balls[][] subboard = new Balls[][]{
                {Balls.WHITE, Balls.BLACK, Balls.BLACK},
                {Balls.EMPTY, Balls.WHITE, Balls.WHITE},
                {Balls.EMPTY, Balls.EMPTY, Balls.WHITE},
        };

        assertEquals(Arrays.deepToString(subboard), Arrays.deepToString(board.getSubBoard(4)));

    }

    /**
     * This method checks if the rotation function is implemented correctly.
     */
    @Test
    public void testRotate() {
        board.setBoard("0~1~-1~-1~-1~-1" +
                "~-1~-0~-1~-1~-1~-1" +
                "~-1~-1~-0~-1~-1~-1" +
                "~1~0~0~1~-0~1" +
                "~-1~1~1~1~-0~-1" +
                "~-1~-1~1~1~-0~1");
        Balls[][] subboard = new Balls[][]{
                {Balls.EMPTY, Balls.EMPTY, Balls.BLACK},
                {Balls.WHITE, Balls.BLACK, Balls.EMPTY},
                {Balls.BLACK, Balls.EMPTY, Balls.EMPTY},
        };

        //For each of the directions possible
        board.rotate(0);
        assertEquals(Arrays.deepToString(subboard), Arrays.deepToString(board.getSubBoard(0)));
        subboard = new Balls[][]{
                {Balls.BLACK, Balls.WHITE, Balls.EMPTY},
                {Balls.EMPTY, Balls.BLACK, Balls.EMPTY},
                {Balls.EMPTY, Balls.EMPTY, Balls.BLACK},
        };
        board.rotate(1);
        assertEquals(Arrays.deepToString(subboard), Arrays.deepToString(board.getSubBoard(1)));
        subboard = new Balls[][]{
                {Balls.EMPTY, Balls.EMPTY, Balls.EMPTY},
                {Balls.EMPTY, Balls.EMPTY, Balls.EMPTY},
                {Balls.EMPTY, Balls.EMPTY, Balls.EMPTY},
        };
        board.rotate(2);
        assertEquals(Arrays.deepToString(subboard), Arrays.deepToString(board.getSubBoard(3)));
        subboard = new Balls[][]{
                {Balls.EMPTY, Balls.EMPTY, Balls.EMPTY},
                {Balls.EMPTY, Balls.EMPTY, Balls.EMPTY},
                {Balls.EMPTY, Balls.EMPTY, Balls.EMPTY},
        };
        board.rotate(3);
        assertEquals(Arrays.deepToString(subboard), Arrays.deepToString(board.getSubBoard(3)));
        subboard = new Balls[][]{
                {Balls.BLACK, Balls.WHITE, Balls.WHITE},
                {Balls.BLACK, Balls.WHITE, Balls.EMPTY},
                {Balls.WHITE, Balls.EMPTY, Balls.EMPTY},
        };
        board.rotate(4);
        assertEquals(Arrays.deepToString(subboard), Arrays.deepToString(board.getSubBoard(4)));
        subboard = new Balls[][]{
                {Balls.WHITE, Balls.BLACK, Balls.BLACK},
                {Balls.EMPTY, Balls.WHITE, Balls.WHITE},
                {Balls.EMPTY, Balls.EMPTY, Balls.WHITE},
        };
        board.rotate(5);
        assertEquals(Arrays.deepToString(subboard), Arrays.deepToString(board.getSubBoard(5)));
        subboard = new Balls[][]{
                {Balls.WHITE, Balls.EMPTY, Balls.WHITE},
                {Balls.BLACK, Balls.BLACK, Balls.BLACK},
                {Balls.WHITE, Balls.WHITE, Balls.WHITE},
        };
        board.rotate(6);
        assertEquals(Arrays.deepToString(subboard), Arrays.deepToString(board.getSubBoard(6)));
        subboard = new Balls[][]{
                {Balls.WHITE, Balls.BLACK, Balls.WHITE},
                {Balls.WHITE, Balls.BLACK, Balls.EMPTY},
                {Balls.WHITE, Balls.BLACK, Balls.WHITE},
        };
        board.rotate(7);
        assertEquals(Arrays.deepToString(subboard), Arrays.deepToString(board.getSubBoard(7)));
    }
}
