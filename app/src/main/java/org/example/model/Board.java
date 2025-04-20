package org.example.model;


/**
 * This class contains all the logic of the board and how it's designed.
 */
public class Board {
    public final int size = 6;
    private Balls[][] fields;
    private static final String[] NUMBERING = {
        "  0  |  1 |  2 |  3 |  4 |  5 ",
        "  6  |  7 |  8 |  9 | 10 | 11",
        " 12  | 13 | 14 | 15 | 16 | 17 ",
        " 18  | 19 | 20 | 21 | 22 | 23 ",
        " 24  | 25 | 26 | 27 | 28 | 29 ",
        " 30  | 31 | 32 | 33 | 34 | 35 "
    };
    private static final String DISTANCE = "               ";

    /**
     * The constructor that creates the board object.
     */
    public Board() {
        fields = new Balls[size][size];
    }

    /**
     * This is a method that generates the fields inside the board object containing EMPTY balls.
     */
    public void generateBoard() {
        for (int row = 0; row < size; row++) {
            for (int col = 0; col < size; col++) {
                fields[row][col] = Balls.EMPTY;
            }
        }
    }

    /**
     * This method sets the board to a specified board by using strings.
     * @param board is a String that represents the board.
     */
    /*@ requires board.length() == 71;
        */
    public void setBoard(String board) {
        String[] split = board.split("~");
        int nr = 0;
        for (int row = 0; row < size; row++) {
            for (int col = 0; col < size; col++) {
                switch (Integer.parseInt(split[nr])) {
                    case 0 -> {
                        setBall(row, col, Balls.indexToBall(0));
                        nr++;
                    }
                    case 1 -> {
                        setBall(row, col, Balls.indexToBall(1));
                        nr++;
                    }
                    case -1 -> {
                        setBall(row, col, Balls.indexToBall(-1));
                        nr++;
                    }
                }
            }
        }
    }

    /**
     *
     * This method returns a 3 by 3 subBoard based on the input.
     * @param subboard a number from 0 to 7.
     * @return Balls[3][3] of the subBoard asked.
     */
    //@ requires subboard >= 0 && subboard <= 7;
    //@ensures \result == getSubBoard(subboard);
    /*@ pure */
    public Balls[][] getSubBoard(int subboard) {
        Balls[][] subBoard = new Balls[3][3];
        if (subboard >= 0 && subboard <= 1) {
            //top left quadrant
            for (int row = 0; row <= 2; row++) {
                for (int col = 0; col <= 2; col++) {
                    subBoard[row][col] = this.getBall(row, col);
                }
            }
        } else if (subboard >= 2 && subboard <= 3) {
            //top right quadrant
            for (int row = 0; row <= 2; row++) {
                for (int col = 3; col < size; col++) {
                    subBoard[row][col - 3] = this.getBall(row, col);
                }
            }
        } else if (subboard >= 4 && subboard <= 5) {
            //bottom left quadrant
            for (int row = 3; row < size; row++) {
                for (int col = 0; col <= 2; col++) {
                    subBoard[row - 3][col] = this.getBall(row, col);
                }
            }
        } else if (subboard >= 6 && subboard <= 7) {
            //bottom right quadrant
            for (int row = 3; row < size; row++) {
                for (int col = 3; col < size; col++) {
                    subBoard[row - 3][col - 3] = this.getBall(row, col);
                }
            }
        }
        return subBoard;
    }

    /**
     * This method sets the values of the board to the new values of the passed Balls[][]
     * object and giving the quadrant to be replaced.
     * @param quadrant a number from 0 to 7. Choosing the subBoard.
     * @param subBoard The Balls[3][3] we want to set inside the board.
     */
    //@ ensures subBoard.equals(getSubBoard(quadrant));
    //@ requires quadrant >= 0 && quadrant <= 7;
    //@ requires subBoard.length == 3;
/*@ pure */
    public void setSubBoard(int quadrant, Balls[][] subBoard) {
        if (quadrant >= 0 && quadrant <= 1) {
            //top left quadrant
            for (int row = 0; row <= 2; row++) {
                for (int col = 0; col <= 2; col++) {
                    setBall(row, col, subBoard[row][col]);
                }
            }
        } else if (quadrant >= 2 && quadrant <= 3) {
            //top right quadrant
            for (int row = 0; row <= 2; row++) {
                for (int col = 3; col < size; col++) {
                    setBall(row, col, subBoard[row][col - 3]);
                }
            }
        } else if (quadrant >= 4 && quadrant <= 5) {
            //bottom left quadrant
            for (int row = 3; row < size; row++) {
                for (int col = 0; col <= 2; col++) {
                    setBall(row, col, subBoard[row - 3][col]);
                }
            }
        } else if (quadrant >= 6 && quadrant <= 7) {
            //bottom right quadrant
            for (int row = 3; row < size; row++) {
                for (int col = 3; col < size; col++) {
                    setBall(row, col, subBoard[row - 3][col - 3]);
                }
            }
        }
    }

    /**
     * This method rotates the array of balls depending on the direction.
     * Clockwise or Counter-Clockwise.
     * @param direction 1 or 0 for ClockWise and CounterClockwise respectively.
     */
    /*@ requires direction >= 0 && direction <= 1;
        ensures \old(getSubBoard(direction)) != getSubBoard(direction);
        */
    public void rotate(int direction) {
        Balls[][] rotate = getSubBoard(direction);
        Balls[][] copy;
        int row;
        int col;
        if (direction % 2 == 0) {
            //counterclockwise rotation
            row = rotate.length;
            col = rotate[0].length;
            copy = new Balls[row][col];
            for (int i = 0; i < row; i++) {
                for (int j = 0; j < col; j++) {
                    copy[(row - 1) - j][i] = rotate[i][j];
                }
            }
        } else {
            //clockwise rotation
            row = size / 2;
            col = size / 2;
            copy = new Balls[col][row];
            for (int i = 0; i < row; i++) {
                for (int j = 0; j < col; j++) {

                    copy[j][row - 1 - i] = rotate[i][j];
                }
            }
        }
        setSubBoard(direction, copy);
    }

    /**
     * This method checks for the current player and his row and col values
     * from the last move made in 4 directions up left.
     * @return the current player if he won the game or null if he did not.
     */
    //@ ensures \result == true || \result == false;
    //@ requires ball != null;
/*@ pure */
    public boolean isWinner(Balls ball) {
        for (int row = 0; row < size; row++) {
            for (int col = 0; col < size; col++) {
                // a vertical line
                if (count(ball, row, col, 1, 0) >= 5) {
                    return true;
                }
                // a horizontal line
                if (count(ball, row, col, 0, 1) >= 5) {
                    return true;
                }
                // a diagonal from bottom-left to top-right
                if (count(ball, row, col, 1, -1) >= 5) {
                    return true;
                }
                // a diagonal from top-left to bottom-right
                if (count(ball, row, col, 1, 1) >= 5) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * This method counts the number of balls in a row for the current player.
     * @param row this is the value of the last move's row
     * @param col this is the value of the last move's col
     * @param dirX this is the direction in which to look for balls
     * @param dirY this is the direction in which to look for balls
     * @return a value between 0 and 6 which is the number of balls in a line.
     */
    //@ ensures \result >= 0 && \result < 7;
    //@ requires dirX == 0 || dirX == 1;
    //@ requires dirY == 0 || dirY == 1 || dirY == -1;
    //@ requires row >= 0 && row <= 5;
    //@ requires col >= 0 && col <= 5;
    //@ requires ball != null;
/*@ pure */
    public int count(Balls ball, int row, int col, int dirX, int dirY) {
        int counter = -1;
        if (getBall(row, col).equals(ball)) {
            counter = 1;
        }

        int r;
        int c;

        r = row + dirX;
        c = col + dirY;
        //this while goes in one direction on the line we are checking
        while (r >= 0 && r < size && c >= 0 && c < size && getBall(r, c).equals(ball)) {
            counter++;
            r += dirX;
            c += dirY;
        }

        r = row - dirX;
        c = col - dirY;
        //this while goes in the other direction on the line we are checking
        while (r >= 0 && r < size && c >= 0 && c < size && getBall(r, c).equals(ball)) {
            counter++;
            r -= dirX;
            c -= dirY;
        }

        return counter;
    }

    /**
     * This method checks weather the board has no more space available.
     * @return true if the board is NOT full otherwise false
     */
    //@ ensures \result == true || \result == false;
    public boolean boardIsFull() {
        int c = -1;
        for (int i = 0; i < size; i++) {
            for (int j = 0; j < size; j++) {
                if (getBall(i, j).equals(Balls.EMPTY)) {
                    if (c == -1) {
                        c = 0;
                    }
                    c++;
                }
            }
        }
        return c == -1;
    }

    /**
     * This method checks weather any player has 5 balls in a row.
     * @return true if there is a winner or false otherwise.
     */
    //@ ensures \result == true || \result == false;
    public boolean fiveInARow() {
        return isWinner(Balls.WHITE) || isWinner(Balls.BLACK);
    }

    /**
     * This method places the marble on the board based on the move.
     * @param move the index of the square.
     */
    //@ ensures \old(getBall(move / size, move % size)) == Balls.EMPTY;
    //@ ensures getBall(move / size, move % size) == ball;
    //@ requires move >= 0 && move <= 35;
    //@ requires ball != null;
    public void move(int move, Balls ball) {
        //the row and columns can be defined from the index like this:
        int lastRow = move / size;
        int lastCol = move % size;
        setBall(lastRow, lastCol, ball);
    }

    /**
     * Basic copy method.
     * @return a Ball array that is the copy of the board.
     */
    public Balls[][] copy() {
        Balls[][] output = new Balls[size][size];
        for (int i = 0; i < size; i++) {
            //I had to make it like this because of a checkstyle error.
            output[i][0] = fields[i][0];
            output[i][1] = fields[i][1];
            output[i][2] = fields[i][2];
            output[i][3] = fields[i][3];
            output[i][4] = fields[i][4];
            output[i][5] = fields[i][5];
        }
        return output;
    }

    public void setFields(Balls[][] fields) {
        this.fields = fields;
    }

    /*@ pure */
    public Balls getBall(int row, int col) {
        return fields[row][col];
    }
    public void setBall(int row, int col, Balls b) {
        fields[row][col] = b;
    }

    public String toString() {
        StringBuilder line = new StringBuilder();
        for (int i = 0; i < size; i++) {
            for (int j = 0; j < size; j++) {
                line.append(fields[i][j].getNumColor()).append(Balls.DISTANCE);
            }
            line.append(DISTANCE).append(NUMBERING[i]);
            line.append("\n");
        }
        return line.toString();
    }
}
