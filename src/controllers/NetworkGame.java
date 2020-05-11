package controllers;

import java.util.ArrayList;
import java.util.Observable;

import models.Board;
import models.ChangeListener;
import models.Protocol;
import models.Ring;
import views.ViewTUI;

/**
 * NetworkGame class. 
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 * 
 */
public class NetworkGame extends Observable implements ChangeListener {
	// ------------------ Instance variables ----------------
	private int playerCount;
	private int currentPlayer;
	private int[] pointsForPlayers; // Points of the players
	
	private boolean firstMove;
	private boolean[] missedMove;
	private boolean[] moveMade;

	/*@ private invariant humanNames.size() >= 2 && humanNames.size() <= 4;*/
	private ArrayList<String> humanNames; // All of the players names
	/*@ private invariant handlers.size() >= 2 && handlers.size() <= 4;*/
	private ArrayList<ServerThread> handlers; // Handlers used to find players
	/*@ private invariant players.size() >= 2 && players.size() <= 4;*/
	private ArrayList<Player> players; // Players that are playing the game
	
	private ViewTUI view;
	
	/*@ private invariant board != null; */
	private Board board;

	// -- Constructor -----------------------------------------------
	/**
	 * Creates a new Network Game object.
	 * @param playercount 
	 * @param humanNames The players names
	 * @param clientHandlers The players handlers which receive their input
	 */
	/*
	 *@ requires playercount >= 2 && playerCount <= 4 && 
	 typesOfPlayers != null && humanNames != null &&
	 humanNames.size() == playercount && clientHandles.size() == playercount; */
	public NetworkGame(int playercount, ArrayList<String> names,
			ArrayList<ServerThread> clientHandlers) {
		
		assert playercount <= 2 && playercount >= 4;
		assert humanNames != null && clientHandlers != null;
		assert playercount == humanNames.size() && playerCount == clientHandlers.size();
		
		playerCount = playercount;
		players = new ArrayList<Player>();
		moveMade = new boolean[playerCount];
		board = new Board(playerCount);
		missedMove = new boolean[playercount];
		handlers = clientHandlers;
		humanNames = names;
		pointsForPlayers = new int[playercount];
		view = new ViewTUI(this);
		addObserver(view);
		view.println("Making a game with " + playercount + " players");
		for (int i = 0; i < playerCount; i++) {
			handlers.get(i).setChangeListener(this);
			moveMade[i] = false;
		}
		for (int i = 0; i < playerCount; i++) {
			pointsForPlayers[i] = 0;
			missedMove[i] = false;
			players.add(new NetworkPlayer(i + 1, humanNames.get(i),
					clientHandlers.get(i)));
		}
	}

	// -- Commands ---------------------------------------------------

	/**
	 * Starts the Ringgz game. Asks after each game if user want to play again.
	 */
	public void startGame() {
		boolean playingGame = true;
		playerInfo();
		while (playingGame) {
			reset();
			setupPlayers();
			play();
			playingGame = playAgain();
			if (playingGame) {
				String allNames = ""; 
				for (int i = 0; i < handlers.size(); i++) {
					allNames += handlers.get(i).getName() + " "; 
				}
				String message;
				for (int i = 0; i < handlers.size(); i++) {
					message = String.format(Protocol.START_GAME + " " + "%d" + " ", i + 1);
					message = message + allNames;
					view.println("New game: " + message);
					Server.sendToClient(handlers.get(i), message);
				}
			}
		}
	}

	/**
	 * Waits for input from all of the players, if all answer with true then the game is restarted.
	 */
	/*@ ensures \result || !\result; */
	private boolean playAgain() {
		boolean condition = false;
		int counter = 0;
		boolean[] playerChoices = new boolean[playerCount];
		int choice;
		do {
			counter = 0;
			for (int i = 0; i < playerChoices.length; i++) {
				choice = handlers.get(i).getPlayAgain();
				switch (choice) {
					case 1 :
						playerChoices[i] = true;
						counter++;
						break;
					case 2 :
						playerChoices[i] = false;
						counter++;
						break;
				}
			}
			condition = counter == playerCount;
		} while (!condition);

		for (int i = 0; i < playerChoices.length; i++) {
			if (!playerChoices[i]) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Returns true if the game is over. The game is over when all players have
	 * no more rings.
	 *
	 * @return true if the game is over
	 */
	/*@ ensures \result || !\result; */
	public boolean gameOver() {
		for (boolean missed : missedMove) {
			if (!missed) {
				return false;
			}
		}
		view.println("Game Over!");
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
			view.print(letter + " = " + colorsInteger.get(i));
			if (i != colorsInteger.size() - 1) {
				view.print(", ");
			}
		}
		view.println("]");

		// Print the available moves
		view.println("Available moves: "
				+ board.availableMoves(players.get(currentPlayer)) + "\n");
	}

	/**
	 * Plays the Ringgz game.
	 * The empty board is shown. Then players play until the game ends
	 */
	private void play() {
		update(-1, -1, -1, -1); // Print the board
		while (!gameOver()) {
			view.println("Current player: " + (1 + currentPlayer));
			if (firstMove || board.availableMoves(players.get(currentPlayer))
					.size() != 0) {

				handlers.get(currentPlayer).setIsTurn(true);
				String tempMessage = Protocol.PLAYER_TURN + " "
						+ (currentPlayer + 1);
				Server.sendToGamers(handlers, tempMessage);

				displayDetails();
				missedMove[currentPlayer] = false;

				int[] move = new int[4];
				String message; // Input from the Client
				boolean acceptable = false;
				String userMove = null;

				do {
					for (int i = 0; i < move.length; i++) {
						move[i] = -1;
					}
					
					if (handlers.get(currentPlayer)
								.getAttemptedMove() != null) {
							
						userMove = handlers.get(currentPlayer)
									.getAttemptedMove();
						handlers.get(currentPlayer).resetAttemptedMove();
							
						if (firstMove) {
							move = validateFirstMove(userMove);
						} else {
							move = validateMove(userMove);
						}
						
						acceptable = move[0] != -1; // Move was accepted
						if (!acceptable) {
							message = Protocol.MOVE_ACCEPTABLE + " "
									+ acceptable;
							Server.sendToClient(handlers.get(currentPlayer),
									message);
							continue;
						}
					}	
				} while (!acceptable);

				// Move was accepted and will now be sent to other players
				message = Protocol.MOVE_ACCEPTABLE + " " + acceptable;
				Server.sendToClient(handlers.get(currentPlayer), message);
				handlers.get(currentPlayer).setIsTurn(false);
				handlers.get(currentPlayer).setMove();
				String moveToSend = "MOVE" + " " + move[0] + " " + move[1] + " "
						+ move[2] + " " + move[3];
				Server.sendToGamers(handlers, moveToSend);
				if (firstMove) {
					firstMove = false;
				}
				handlers.get(currentPlayer).resetMove();

				board = players.get(currentPlayer).makeBoardMove(userMove,
						board);
				// Update the board with the move
				update(move[0], move[1], move[2], move[3]);
			} else {
				view.println(players.get(currentPlayer).getPlayerName()
						+ " has no available moves!");
				missedMove[currentPlayer] = true;
			}
			currentPlayer = (currentPlayer + 1) % getPlayerCount();
		}
		printResult();
	}

	/**
	 * Method for writing who is playing.
	 */
	/*@ pure */
	private void playerInfo() {
		for (int i = 0; i < players.size(); i++) {
			ViewTUI.staticPrint(players.get(i).getPlayerName());
			if (i != players.size() - 1) {
				ViewTUI.staticPrint(" vs. ");
			}
		}
		view.println("");
	}

	/**
	 * Resets the game.
	 * The board is emptied and a random player becomes the current player.
	 */
	private void reset() {
		currentPlayer = (int) (Math.random() * playerCount);
		firstMove = true;
		players = new ArrayList<>();
		for (int i = 0; i < playerCount; i++) {
			pointsForPlayers[i] = 0;
			moveMade[i] = false;
			players.add(new NetworkPlayer(i + 1, humanNames.get(i),
					handlers.get(i)));
			players.get(i).clearRings();
			players.get(i).clearColors();
			missedMove[i] = false;
		}
		board.reset();
	}

	/**
	 * Method for validating the first move.
	 * @param string Move input by Client
	 * @return int[] of the move values Color Size X Y
	 */
	/*@ requires string != null; */
	/*@ ensures \result != null; */
	private int[] validateFirstMove(String string) {
		int[] error = {-1};
		String[] stringArray;
		if (string.equals(null)) {
			return error;
		}

		stringArray = string.split(" ");

		if (stringArray.length != 5) {
			view.println("ERROR: Format was wrong!\n");
			return error;
		}

		int[] parsedInput = new int[stringArray.length - 1];
		int[] result = new int[stringArray.length - 1];

		try {
			char[] numChar;

			for (int i = 1; i < stringArray.length; i++) {
				numChar = stringArray[i].toCharArray();
				for (int j = 0; j < numChar.length; j++) {
					if (Character.isDigit(numChar[j])) {
						parsedInput[i - 1] = Character
								.getNumericValue(numChar[j]);
					} else {
						continue;
					}
				}
			}
		} catch (NullPointerException | NumberFormatException e) {
			e.printStackTrace();
			view.println("ERROR: Format was wrong!\n");
			return error;
		}

		// Check x
		if (parsedInput[2] < 1 || parsedInput[2] > 3) {
			view.println("ERROR: x was invalid!\n");
			return error;
		}

		// Check y
		if (parsedInput[3] < 1 || parsedInput[3] > 3) {
			view.println("ERROR: y was invalid!\n");
			return error;
		}

		result[0] = 0;
		result[1] = 0;
		result[2] = parsedInput[2];
		result[3] = parsedInput[3];

		return result;
	}

	/**
	 * Method for validating a normal move that is not the first move.
	 * @param playerChoice choice of the player
	 * @return int[] of players choice Color Size X Y
	 */
	/*@ requires playerChoice != null; */
	/*@ ensures \result != null;*/
	public int[] validateMove(String playerChoice) {
		int[] error = {-1};

		if (playerChoice.equals(null)) {
			return error;
		}
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
			return error;
		}

		// Check command
		if (!input[0].equals(command)) {
			view.println("ERROR: Command MOVE was wrong!\n");
			return error;
		}

		// Check color
		if (checking[0] < 1 || checking[0] > 4) {
			view.println("ERROR: color was invalid!\n");
			return error;
		}

		// Check size
		if (checking[1] < 0 || checking[1] > 4) {
			view.println("ERROR: size was invalid!\n");
			return error;
		}

		// Check playersRings
		boolean hasRing = false;
		ArrayList<Ring> playersRings = players.get(currentPlayer).getPlayerRings();
		view.println("Player rings amount: " + playersRings.size());
		for (int i = 0; i < playersRings.size(); i++) {
			if (playersRings.get(i).getColor() == checking[0]
					&& playersRings.get(i).getSize() == checking[1]) {
				hasRing = true;
			}
		}

		if (!hasRing) {
			view.println("ERROR: you don't have that ring!\n");
			return error;
		}

		// Check x
		if (checking[2] < 0 || checking[2] > 4) {
			view.println("ERROR: x was invalid!\n");
			return error;
		}

		// Check y
		if (checking[3] < 0 || checking[3] > 4) {
			view.println("ERROR: y was invalid!\n");
			return error;
		}

		// Check if valid place on board
		ArrayList<String> possibleMoves = board
				.availableMoves(players.get(currentPlayer));

		// Check if this move is available
		boolean canPlace = false;
		String storedInput = checking[1] + " " + checking[2] + " "
				+ checking[3];
		for (int i = 0; i < possibleMoves.size(); i++) {
			if (possibleMoves.get(i).equals(storedInput)) {
				canPlace = true;
			}
		}

		if (!canPlace) {
			view.println("ERROR: you can't put ring here!\n");
			return error;
		}

		// DONE CHECKING
		return checking;
	}
	
	/**
	 * Method for setting up a 2 player game that distributes colors and rings.
	 * Player 1 -> Colors: 1,3
	 * Player 2 -> Colors: 2,4
	 */
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
	
	/**
	 * Method for setting up a 3 player game that distributes colors and rings.
	 * Player 1 -> Colors: 1,4
	 * Player 2 -> Colors: 2,4
	 * Player 3 -> Colors: 3,4
	 */
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

	/**
	 * Method for setting up a 4 player game that distributes colors and rings.
	 * Player 1 -> Color: 1
	 * Player 2 -> Color: 2
	 * Player 3 -> Color: 3
	 * Player 4 -> Color: 4
	 */
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

	/**
	 * Method that runs the correct method depending on the player count.
	 */
	private void setupPlayers() {
		players.get(currentPlayer).addStartBase();

		switch (playerCount) {
			case 2 :
				// 2 colors each
				setup2Players();
				break;
			case 3 :
				// 1 color each, split 4th color
				setup3Players();
				break;
			case 4 :
				// 1 color each
				setup4Players();
				break;
		}
	}

	/**
	 * Method for getting the colors of the current player.
	 * @return returns the current players colors
	 */
	/*@ ensures \result != null;*/
	public ArrayList<Integer> getCurrentPlayerColors() {
		return players.get(currentPlayer).getPlayerColors();
	}

	/**
	 * Method that return all the remaining rings in the possesion of a client.
	 * @return array of amounts of rings left per player.
	 */
	/*@ ensures \result.length == getPlayerCount() && \result != null;*/
	public int[] getPlayersRingAmount() {
		int[] ringCount = new int[playerCount];
		for (int i = 0; i < ringCount.length; i++) {
			ringCount[i] = players.get(i).getPlayerRings().size();
		}
		return ringCount;
	}

	/**
	 * Prints the game situation and writes which player did what move.
	 */
	/*@ requires color >= -1 && type >= -1 && x >= -1 && y >= -1;*/
	private void update(int color, int type, int x, int y) {
		String output = "";
		if (color >= 0 && type >= 0) {
			output += players.get(currentPlayer).getPlayerName()
					+ " chose ring type: " + type + ", ring color: " + color
					+ ", on x = " + x + ", y = " + y;
		}
		output += "\ncurrent game situation: \n" + board.toString() + "\n";
		view.println(output);
	}

	/**
	 * Prints the result of the game. 
	 * We get a string containing the winners and then split the concatenated result here.
	 * The winner is either: -1 = draw, 0-3 = winner
	 */
	private void printResult() {
		board.calculatePoints();
		// 
		String winnerPlayerNumber = board.checkForWinner();
		char[] winnerPlayerChar = winnerPlayerNumber.toCharArray();
		int winnerAmount = winnerPlayerChar.length;
		int winnerNumber = Integer.parseInt(winnerPlayerNumber);

		int[] points = board.getPlayerPoints();
		view.println("Points of the game: ");
		for (int i = 0; i < points.length; i++) {
			view.println(players.get(i).getPlayerName() + (i + 1) + " has: "
					+ points[i] + " points");
		}
		view.println("");

		// Someone won the game
		if (winnerNumber != -1) {
			// Check if multiple people won the game
			Player winner;
			if (winnerAmount > 1) {
				view.println(winnerAmount
						+ " players got the same amount of points!");

				int[] winnerRingAmount = getPlayersRingAmount();

				int min = 30;
				boolean minFound = false;
				for (int i = 0; i < winnerRingAmount.length; i++) {
					for (int j = 0; j < winnerAmount; j++) {
						// Found the winner and his rings
						if (i == Character
								.getNumericValue(winnerPlayerChar[j])) {
							view.println(players.get(i).getPlayerName()
									+ " has " + winnerRingAmount[i] + " rings");
							if (winnerRingAmount[i] == min) {
								minFound = false;
							}
							if (winnerRingAmount[i] < min) {
								min = winnerRingAmount[i];
								minFound = true;
								winnerNumber = i;
							}
						}
					}
				}
				// Some winner has the least rings
				if (minFound) {
					winner = players.get(winnerNumber);
					view.println(winner.getPlayerName() + " has won with "
							+ points[winnerNumber] + " points!");
				} else {
					winnerNumber = -1;
					view.println("Draw. There is no winner!");
				}
			} else { // One person won
				winner = players.get(winnerNumber);
				view.println(winner.getPlayerName() + " has won with "
						+ points[winnerNumber] + " points!");
			}
			// No winners
		} else {
			winnerNumber = -1;
			view.println("Draw. There is no winner!");
		}

		String scores = "SCORES " + (winnerNumber + 1) + " ";
		for (int i = 0; i < players.size(); i++) {
			scores += points[i] + " ";
		}
		
		// Send the scores to the Clients
		Server.sendToGamers(handlers, scores);
	}

	/**
	 * @return the playerCount in the game
	 */
	/*@ pure */
	public int getPlayerCount() {
		return playerCount;
	}

	/**
	 * Method that gets run to notify a user has put in a new move.
	 */
	public void onChange() {
		moveMade[currentPlayer] = true;
	}
}
