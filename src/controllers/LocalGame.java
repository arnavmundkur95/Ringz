package controllers;

import java.util.ArrayList;
import java.util.Observable;
import models.Board;
import models.Ring;
import views.ViewTUI;

/**
 * LocalGame class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class LocalGame extends Observable {
	public static final int[] COLORS = {0, 1, 2, 3, 4 };
	private int playerCount;
	private int currentPlayer;
	private int[] pointsForPlayers;
	private boolean firstMove;
	private boolean[] missedMove;
	
	private ArrayList<Player> players;
	private ArrayList<String> humanNames;
	private ViewTUI view;

	/* @ private invariant board != null; */
	private Board board;

	// -- Constructors -----------------------------------------------

	/**
	 * Creates a new Game object.
	 * 
	 * @param s0
	 *            the first player
	 * @param s1
	 *            the second player
	 */
	public LocalGame(int playercount, char[] typesOfPlayers, ArrayList<String> humanNames) {
		playerCount = playercount;
		view = new ViewTUI(this);
		addObserver(view);
		players = new ArrayList<Player>();
		this.humanNames = humanNames;
		pointsForPlayers = new int[playercount];
		view.println("Making a game with " + playerCount + " players");
		board = new Board(playercount);
		missedMove = new boolean[playercount];
		for (int i = 0; i < playerCount; i++) {
			pointsForPlayers[i] = 0;
			missedMove[i] = false;
			if (typesOfPlayers[i] == 'S') {
				players.add(new ComputerPlayer(i + 1, this.humanNames.get(i) + " the Smart"));
			} else if (typesOfPlayers[i] == 'N') {
				players.add(new ComputerPlayer(i + 1, this.humanNames.get(i) + " the Naive"));
			} else if (typesOfPlayers[i] == 'H') {
				players.add(new HumanPlayer(i + 1, this.humanNames.get(i)));
			} 
		}
		startGame();
	}

	// -- Commands ---------------------------------------------------	
	/**
	 * Starts the Ringgz game. Asks after each game if user want to play again
	 */
	public void startGame() {
		boolean playingGame = true;
		playerInfo();
		while (playingGame) {
			reset();
			setupPlayers();
			play();
			playingGame = view.readBoolean("\n> Play another time? (y/n)?", "y", "n");
		}
	}

	/**
	 * Returns true if the game is over. The game is over when all players have no
	 * more rings.
	 *
	 * @return true if the game is over
	 */
	public boolean gameOver() {
		for (boolean missed : missedMove) {
			if (!missed) {
				return false;
			}
		}
		view.println("Game Over!\n");
		return true;
	}
	/**
	 * Method for showing current players' color, available moves.
	 */
	public void displayDetails() {
		Player player = players.get(currentPlayer); 
		// Display the colors of the player
		ArrayList<Integer> colorsInteger = player.getPlayerColors();
		view.println("It is " + player.getPlayerName() + "'s turn");
		view.print("Your colors are: [");
		
		char letter; // Letter of the color
		for (int i = 0; i < colorsInteger.size(); i++) {
			letter = colorsInteger.get(i).toString().toCharArray()[0];
			letter = board.convertNumToChar(letter);
			view.print(colorsInteger.get(i) + " = " + letter);
			if (i != colorsInteger.size() - 1) {
				view.print(", ");
			}
		}
		view.println("]");

		// Print the available moves
		view.println("Available moves: " + board.availableMoves(players.get(currentPlayer)));
	}

	/**
	 * Plays the Ringgz game. <br>
	 * The empty board is shown. Then players play until the game ends
	 */
	private void play() {
		String playerChoice = ""; // "MOVE color type x y"
		update(-1, -1, -1, -1);
		while (!gameOver()) {
			if (firstMove || board.availableMoves(players.get(currentPlayer)).size() != 0) {
				displayDetails();
				missedMove[currentPlayer] = false;
				int[] move = new int[4];
				do {
					if (firstMove) {
						playerChoice = players.get(currentPlayer).determineFirstMove();
						move = validateFirstMove(playerChoice);
					} else {
						playerChoice = players.get(currentPlayer).determineMove(board);
						move = validateMove(playerChoice);
					}
				} while (move == null);

				if (firstMove) {
					firstMove = false;
				}
				players.get(currentPlayer).makeBoardMove(playerChoice, board);
				update(move[0], move[1], move[2], move[3]);
			} else {
				view.print(players.get(currentPlayer).getPlayerName());
				view.println(" has no available moves!");
				missedMove[currentPlayer] = true;
			}
			currentPlayer = (currentPlayer + 1) % playerCount;
		}
		printResult();
	}

	/**
	 * Method for writing who is playing.
	 */
	private void playerInfo() {
		for (int i = 0; i < players.size(); i++) {
			view.print(players.get(i).getPlayerName());
			if (i != players.size() - 1) {
				view.print(" vs. ");
			}
		}
		view.println("");
	}

	

	/**
	 * Resets the game. <br>
	 * The board is emptied and player[0] becomes the current player.
	 */
	private void reset() {
		currentPlayer = (int) (Math.random() * playerCount);
		firstMove = true;
		// Make missed moves to false for each player
		for (int i = 0; i < playerCount; i++) {
			missedMove[i] = false;
			pointsForPlayers[i] = 0;
			players.get(i).clearRings();
			players.get(i).clearColors();
			missedMove[i] = false;
		}
		board.reset();
	}

	private int[] validateFirstMove(String string) {

		String[] stringArray = string.split(" ");

		if (stringArray.length != 5) {
			view.println("ERROR: Format was wrong!\n");
			return null;
		}
		
		int[] parsedInput = new int[stringArray.length - 1];
		int[] result = new int[stringArray.length - 1];
		
		try {
			char[] numChar;
			
			for (int i = 1; i < stringArray.length; i++) {
				numChar = stringArray[i].toCharArray();
				for (int j = 0; j < numChar.length; j++) {
					if (Character.isDigit(numChar[j])) {
						parsedInput[i - 1] = Character.getNumericValue(numChar[j]);
					} else {
						continue;
					}
				}
			}
		} catch (NullPointerException | NumberFormatException e) {
			e.printStackTrace();
			view.println("ERROR: Format was wrong!\n");
			return null;
		}

		// Check x
		if (parsedInput[2] < 1 || parsedInput[2] > 3) {
			view.println("ERROR: x was invalid!\n");
			return null;
		}

		// Check y
		if (parsedInput[3] < 1 || parsedInput[3] > 3) {
			view.println("ERROR: y was invalid!\n");
			return null;
		}

		result[0] = 0;
		result[1] = 0;
		result[2] = parsedInput[2];
		result[3] = parsedInput[3];
		return result;
	}

	private void setup2Players() {
		ArrayList<Ring> ringsForPlayer = new ArrayList<>();
		ArrayList<Integer> colorsForPlayer = new ArrayList<>();

		for (int i = 0; i < players.size(); i++) {
			ringsForPlayer = new ArrayList<>();
			colorsForPlayer = new ArrayList<>();
			 
			// Loop through colors
			for (int j = 0; j < 3; j += 2) {
				// Loop through bases
				for (int k = 0; k < 3; k++) {
					ringsForPlayer.add(new Ring(0, i,
							j + players.get(i).getPlayerNumber(), false));
				}

				// Loop through rings
				for (int k = 0; k < 3; k++) {
					for (int l = 1; l <= 4; l++) {
						ringsForPlayer.add(new Ring(l, i,
								j + players.get(i).getPlayerNumber(), true));
					}
				}
				colorsForPlayer.add(j + players.get(i).getPlayerNumber());
			}

			players.get(i).setRings(ringsForPlayer);
			players.get(i).setColors(colorsForPlayer);
		}
	}

	private void setup3Players() {
		ArrayList<Ring> ringsForPlayer = new ArrayList<>();
		ArrayList<Integer> colorsForPlayer = new ArrayList<>();

		for (int i = 0; i < players.size(); i++) {
			ringsForPlayer = new ArrayList<>();
			colorsForPlayer = new ArrayList<>();

			// Loop through colors
			for (int j = 1 * i + 1; j <= 1 * (i + 1); j++) {

				// Loop through bases
				for (int k = 0; k < 3; k++) {
					ringsForPlayer.add(new Ring(0, i, j, false));
				}

				// Loop through rings
				for (int k = 0; k < 3; k++) {
					for (int l = 1; l <= 4; l++) {
						ringsForPlayer.add(new Ring(l, i, j, true));
					}
				}
				colorsForPlayer.add(j);
			}

			// Loop through last color
			// Loop through bases
			for (int k = 0; k < 1; k++) {
				ringsForPlayer.add(new Ring(0, i, 4, false));
			}

			// Loop through rings
			for (int k = 0; k < 1; k++) {
				for (int l = 1; l <= 4; l++) {
					ringsForPlayer.add(new Ring(l, i, 4, false));
				}
			}
			colorsForPlayer.add(4);
			players.get(i).setRings(ringsForPlayer);
			players.get(i).setColors(colorsForPlayer);
		}
	}

	private void setup4Players() {
		ArrayList<Ring> ringsForPlayer = new ArrayList<>();
		ArrayList<Integer> colorsForPlayer = new ArrayList<>();

		for (int i = 0; i < players.size(); i++) {
			ringsForPlayer = new ArrayList<>();
			colorsForPlayer = new ArrayList<>();

			// Loop through colors
			for (int j = 1 * i + 1; j <= 1 * (i + 1); j++) {

				// Loop through bases
				for (int k = 0; k < 3; k++) {
					ringsForPlayer.add(new Ring(0, i, j, false));
				}

				// Loop through rings
				for (int k = 0; k < 3; k++) {
					for (int l = 1; l <= 4; l++) {
						ringsForPlayer.add(new Ring(l, i, j, true));
					}
				}
				colorsForPlayer.add(j);
			}
			players.get(i).setRings(ringsForPlayer);
			players.get(i).setColors(colorsForPlayer);
		}
	}

	private void setupPlayers() {
		players.get(currentPlayer).addStartBase();

		switch (playerCount) {
			case 2:
				// 2 colors each 1 -> 1,3, 2 -> 2,4
				setup2Players();
				break;
			case 3:
				// 1 color each, split 4th color
				setup3Players();
				break;
			case 4:
				// 1 color each
				setup4Players();
				break;
		}

	}

	public int[] validateMove(String playerChoice) {
		int[] checking = new int[4]; // Array used for checking input

		String[] input;
		String command = "MOVE";
		
		try {
			char[] numChar;
			input = playerChoice.split(" ");
			for (int i = 1; i < input.length; i++) {
				numChar = input[i].toCharArray();
				for (int j = 0; j < numChar.length; j++) {
					if (Character.isDigit(numChar[j])) {
						checking[i - 1] = Character.getNumericValue(numChar[j]);
					} else {
						continue;
					}
				}
			}
		} catch (NullPointerException e) {
			e.printStackTrace();
			view.println("ERROR: Format was wrong!\n");
			return null;
		}

		// Check command
		if (!input[0].equals(command)) {
			view.println("ERROR: Command MOVE was wrong!\n");
			return null;
		}

		// Check color
		if (checking[0] < 1 || checking[0] > 4) {
			view.println("ERROR: color was invalid!\n");
			return null;
		}

		// Check size
		if (checking[1] < 0 || checking[1] > 4) {
			view.println("ERROR: size was invalid!\n");
			return null;
		}

		// Check playersRings
		boolean hasRing = false;
		ArrayList<Ring> playersRings = players.get(currentPlayer).getPlayerRings();
		for (int i = 0; i < playersRings.size(); i++) {
			if (playersRings.get(i).getColor() == checking[0] && 
					playersRings.get(i).getSize() == checking[1]) {
				hasRing = true;
			}
		}

		if (!hasRing) {
			view.println("ERROR: you don't have that ring!\n");
			return null;
		}

		// Check x
		if (checking[2] < 0 || checking[2] > 4) {
			view.println("ERROR: x was invalid!\n");
			return null;
		}

		// Check y
		if (checking[3] < 0 || checking[3] > 4) {
			view.println("ERROR: y was invalid!\n");
			return null;
		}

		// Check if valid place on board
		ArrayList<String> possibleMoves = board.availableMoves(players.get(currentPlayer));

		// Check if this move is available
		boolean canPlace = false;
		String storedInput = checking[1] + " " + checking[2] + " " + checking[3];
		for (int i = 0; i < possibleMoves.size(); i++) {
			if (possibleMoves.get(i).equals(storedInput)) {
				canPlace = true;
			}
		}

		if (!canPlace) {
			view.println("ERROR: you can't put ring here!\n");
			return null;
		}

		// DONE CHECKING
		return checking;
	}

	public ArrayList<Integer> getCurrentPlayerColors() {
		return players.get(currentPlayer).getPlayerColors();
	}
	
	public int[] getPlayersRingAmount() {
		int[] ringCount = new int[playerCount];
		for (int i = 0; i < playerCount; i++) {
			ringCount[i] = players.get(i).getPlayerRings().size();
		}
		return ringCount;
	}

	/**
	 * Prints the game situation.
	 */
	private void update(int color, int type, int x, int y) {
		String output = "";
		if (color >= 0 && type >= 0) {
			output += players.get(currentPlayer).getPlayerName() + " chose ring type: " + type
					+ ", ring color: " + color + ", on x = " + x + ", y = " + y;
		}
		output += "\ncurrent game situation: \n" + board.toString() + "\n";
		view.println(output);
	}

	/**
	 * Prints the result of the game. <br>
	 */
	private void printResult() {
		board.calculatePoints();
		// -1 = no winner, 0-3 = winner, 01;02;03;12;13 
		String winnerPlayerNumber = board.checkForWinner();
		char[] winnerPlayerChar = winnerPlayerNumber.toCharArray();
		int winnerAmount = winnerPlayerChar.length;
		int winnerNumber = Integer.parseInt(winnerPlayerNumber);
		
		int[] points = board.getPlayerPoints();
		view.println("Points of the game: ");
		for (int i = 0; i < points.length; i++) {
			view.print(players.get(i).getPlayerName() + (i + 1));
			view.println(" has: " + points[i] + " points");
		}
		view.println("");
		
		// Someone won the game
		if (winnerNumber != -1) {
			// Check if multiple people won the game
			Player winner;
			if (winnerAmount > 1) {
				view.println(winnerAmount + " players got the same amount of points!");
				int[] winnerRingAmount = getPlayersRingAmount();
				int min = 30;
				int winnerNr = -1;
				boolean minFound = false;
				for (int i = 0; i < winnerRingAmount.length; i++) {
					for (int j = 0; j < winnerAmount; j++) {
						// Found the winner and his rings
						if (i == Character.getNumericValue(winnerPlayerChar[j])) {
							view.print(players.get(i).getPlayerName() + " has ");
							view.println(winnerRingAmount[i] + " rings");
							if (winnerRingAmount[i] == min) {
								minFound = false;
							}
							if (winnerRingAmount[i] < min) {
								min = winnerRingAmount[i];
								minFound = true;
								winnerNr = i;
							}
						}
					}
				}
				
				view.println("");
				
				if (minFound) {
					winner = players.get(winnerNr);
					view.print(winner.getPlayerName() + " has won with ");
					view.println(points[winnerNr] + " points!");
				} else {
					view.println("Draw. There is no winner!");
				}			
			} else {
				winner = players.get(winnerNumber);
				view.print(winner.getPlayerName() + " has won with ");
				view.println(points[winnerNumber] + " points!");
			}
			
		// No winners
		} else {
			view.println("Draw. There is no winner!");
		}
	}
}
