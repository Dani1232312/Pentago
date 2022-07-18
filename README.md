# Resit-11

# Solo game

To start an offline game. Run the Pentago class inside the run package.
After starting the application follow the prompts that are being show on the Textual User Interface.

At any point you could type HELP so that the help menu is being shown as below:

`HELP MENU:`

`CHANGE to change AI difficulty`

`MOVE~nr~nr`

`HINT  to request a move from the AI`


To get a hint from the AI, firstly you would have to activate it, by typing CHANGE.
This command will show on the Interface what the difficulty AI has been set to. (Smart/Naive/off)

In case a user has forgotten the values that can be introduced inside the move command these will be shown below as well 
as in the program by typing help.

`B := 0 means rotate the top left subboard counter-clockwise  `

`B := 1 means rotate the top left subboard clockwise`

`B := 2 means rotate the top right subboard counter-clockwise`

`B := 3 means rotate the top right subboard clockwise`

`B := 4 means rotate the bottom left subboard counter-clockwise`

`B := 5 means rotate the bottom left subboard clockwise`

`B := 6 means rotate the bottom right subboard counter-clockwise`

`B := 7 means rotate the bottom right subboard clockwise`

`"  0  |  1 |  2 |  3 |  4 |  5 ",`

`"  6  |  7 |  8 |  9 | 10 | 11",`

`" 12  | 13 | 14 | 15 | 16 | 17 ",`

`" 18  | 19 | 20 | 21 | 22 | 23 ",`

`" 24  | 25 | 26 | 27 | 28 | 29 ",`

`" 30  | 31 | 32 | 33 | 34 | 35 "`

# Online Game (Client)

To start a Client to play on the reference server run the ClientTUI class inside the run package.
From there once again follow the prompts on the screen. They require an ip address and port.

To AUTOQUEUE as the AI on the server. After doing the initial handshake protocol with the server.

`HELLO~description`

`LOGIN~name`

Firstly you would have to activate the AI on the client. This can be done by typing:
`AI` in the TUI, these commands also provide feedback.
After the AI has been activated you have to change the difficulty of the AI. Initially after 
activating the AI it won't work as no Strategy has been selected.

There are two types of AI: Naive and Smart. You can cycle through these options by
inputting `CHANGE` in the TUI, and select your desired difficulty.

After these commands you can start the `QUEUE` command, which will join the QUEUE on the server.
After some time you should see a game has started and the AI will play continuously without interruption unless
the `AI`, `Change` or `QUIT` commands have been provided.

To run the tests simply run the whole class. Except for the ClientTest where the two methods
should be run separately.

