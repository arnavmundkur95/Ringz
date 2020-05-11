package controllers;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.ArrayList;

import models.Board;
import models.Protocol;
import models.Ring;
import views.ViewTUI;

/**
 * Client class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class Client {
	private static final String USAGE = "Usage: <address> <port>";
	private static int turnCounter = 0;
	private int playerNumber;
	private int currentPlayer;
	private boolean turn;
	private boolean humanMoveAccepted = false;
	private Board board;
	private Player player;
	private String playerType = null;
	private PrintWriter printWriter;
	private ArrayList<Ring> playerRings = new ArrayList<>();
	private ArrayList<Integer> playerColors = new ArrayList<>();
	private String attemptedMove;

	public void joinServer(String[] args) {
		turn = false;
		String name = null; // Name of the user
		InetAddress addr = null; // IP where we want to connect
		String portNumber;
		playerType = null;
		int port = 0;
		Socket sock = null;

		// Step 1: Address of the Server
		String serverAddress;
		try {
			if (args.length == 2) {
				addr = InetAddress.getByName(args[0]);
				ViewTUI.staticPrintline("Address: " + addr);
			} else if (args.length == 0) {
				serverAddress = ViewTUI.readString("Enter the IP of Server: ");
				addr = InetAddress.getByName(serverAddress);
			} else {
				ViewTUI.staticPrintline(USAGE);
				ViewTUI.staticPrintline("ERROR: too make input parameters");
				System.exit(0);
			}
		} catch (UnknownHostException e) {
			ViewTUI.staticPrintline(USAGE);
			ViewTUI.staticPrintline("ERROR: host " + args[0] + " unknown");
			System.exit(0);
		}

		boolean validSetup = false;
		// Step 2: Port of the server
		do {
			if (args.length > 2) {
				portNumber = args[1];
			} else {
				portNumber = ViewTUI.readString("Enter the port of the Server: ");
				boolean goodPlayer = false;
				do {
					ViewTUI.staticPrintline("Enter whether you would like to be a human, "
							+ "smart computer or naive computer player");
					playerType = ViewTUI.readString("H -> Human, N -> Naive Computer,"
							+ " S -> Smart Computer");

					if (playerType.equals("H")) {

						player = new HumanPlayer(playerNumber, name);
						goodPlayer = true;
						playerType = "H";
					} else if (playerType.equals("N")) {

						player = new ComputerPlayer(playerNumber, name, printWriter);
						goodPlayer = true;
						
					} else if (playerType.equals("S")) {

						ViewTUI.staticPrintline("Sorry we have not implemented "
								+ "a Smart Computer player, please choose again");
						playerType = ViewTUI.readString("H -> Human, N -> Naive Computer ");
					}

					playerType = playerType.toUpperCase();

				} while (!goodPlayer);
				name = ViewTUI.readString("Please enter your name: ");
			}
			// parse args[2] - the port
			port = getPort(portNumber);
			if (port == 0) {
				ViewTUI.staticPrintline(USAGE);
				ViewTUI.staticPrintline("ERROR: port " + portNumber + " is not an integer");
				continue;
			}
			validSetup = true;

		} while (!validSetup);
		
		
		// try to open a Socket to the server
		try {
			sock = new Socket(addr, port);
			printWriter = new PrintWriter(sock.getOutputStream());
			InputStreamReader inputStreamReader = new InputStreamReader(sock.getInputStream());
			BufferedReader serverReader = new BufferedReader(inputStreamReader);
			
			if (playerType.equals("H")) {
				// Step 3: Check what the user supports
				boolean[] clientSupports = ViewTUI.readBooleans(
						"Do you support: SUPPORTS encryption chat challenge leaderboard: ");

				String supported = "SUPPORTS ";

				for (int i = 0; i < clientSupports.length; i++) {
					supported += clientSupports[i] + " ";
				}
				sendToGame(supported);
			} else if (playerType.equals("N") || playerType.equals("S")) {
				sendToGame("SUPPORTS false false false false");
			}

			while (true) {
				// Interpret all messages from server here
				String message = serverReader.readLine();
				ViewTUI.staticPrintline(message);
				String[] splitMessage = message.split(" ");

				if (splitMessage[0].equals(Protocol.START_GAME)) {
					playerNumber = Integer.parseInt(splitMessage[1]);
					ViewTUI.staticPrintline("My playernumber: " + playerNumber);
					name = splitMessage[playerNumber + 1];
					if (playerType.equals("H")) {
						player = new HumanPlayer(playerNumber, name);
					} else if (playerType.equals("N") || playerType.equals("S")) {
						player = new ComputerPlayer(playerNumber, name, printWriter);
					}

					int playerAmount = splitMessage.length - 2;
					turnCounter = 0;
					playerColors = new ArrayList<>();
					playerRings = new ArrayList<>();
					
					board = new Board(playerAmount);
					ViewTUI.staticPrintline(board.toString());
					
					newGameRings(splitMessage.length - 2, playerNumber);
					
					// Setting up a game if a human plays it
					if (player.getClass().getName().equals("controllers.HumanPlayer")) {
						SystemInThread sin = new SystemInThread(printWriter);
						sin.start();	
					} 
					player.setRings(playerRings);
					player.setColors(playerColors);
					
				} else if (splitMessage[0].equals(Protocol.PLAYER_TURN)) {
					currentPlayer = Integer.parseInt(splitMessage[1]);
					turnCounter++;
					if (currentPlayer == playerNumber) {
						if (turnCounter == 1) {
							boolean hasRing = false;
							for (int i = 0; i < player.getPlayerRings().size(); i++) {
								if (player.getPlayerRings().get(i).getSize() == 0
										&& player.getPlayerRings().get(i).getColor() == 0) {
									hasRing = true;
								}
							}
							if (!hasRing) {
								player.addStartBase();
							}
						}
						if (player.getClass().getName().contains("HumanPlayer")) {
							ViewTUI.staticPrintline(board.availableMoves(player).toString());
							if (turnCounter == 1) {
								ViewTUI.staticPrintline("Please make first move: MOVE 0 0 X Y ");
		
							} else {
								ViewTUI.staticPrintline("Please make a move: MOVE COLOR SIZE X Y ");
							
							}
						} else if (player.getClass().getName().contains("ComputerPlayer")) {
							ViewTUI.staticPrintline("My rings; " + player.getPlayerRings());
							ViewTUI.staticPrintline("I have: " + 
									player.getPlayerRings().size() + " rings");
							attemptedMove = player.makeMoveWithBoard(turnCounter, board);
						}
					}

				} else if (splitMessage[0].equals(Protocol.MOVE)) { // Move from other player
					if (humanMoveAccepted) {
						board = player.makeBoardMove(message, board);
						humanMoveAccepted = false;
					}
					if (turn) {
						board = player.makeBoardMove(message, board);
					} else {
						board = player.makeEnemyMove(message, board, currentPlayer);
					}
					ViewTUI.staticPrintline(board.toString());
				} else if (splitMessage[0].equals(Protocol.MOVE_ACCEPTABLE)) {
					if (splitMessage[1].equals("false")) {
						if (player.getClass().getName().contains("HumanPlayer")) {
							if (turnCounter == 1) {
								ViewTUI.staticPrintline("Please make first move: MOVE 0 0 X Y ");
		
							} else {
								ViewTUI.staticPrintline("Please make a move: MOVE COLOR SIZE X Y ");
							}
							
						} else if (player.getClass().getName().contains("ComputerPlayer")) {
							attemptedMove = player.makeMoveWithBoard(turnCounter, board);
						}
					} else if (splitMessage[1].equals("true")) {
						
						// MOVE WAS GOOD
						if (player.getClass().getName().contains("HumanPlayer")) {
							humanMoveAccepted = true;
							
						} else if (player.getClass().getName().contains("ComputerPlayer")) {
							board = player.makeBoardMove(attemptedMove, board);
							attemptedMove = null;
						}				
						
					}
				} else if (splitMessage[0].equals(Protocol.SUPPORTS)) {
					playerType = playerType.toUpperCase();
					if (playerType.equals("H")) {
						String lobbyChoice = null;
						boolean goodConnection = false;
						do {
							lobbyChoice = ViewTUI.readString(
									"Please fill in the lobby number you would like to enter: ");

							if (Integer.parseInt(lobbyChoice) >= 0 &&
									Integer.parseInt(lobbyChoice) < 5) {
								goodConnection = true;
							}

						} while (!goodConnection);

						sendToGame("CONNECT " + name + " " + lobbyChoice);

					} else if (playerType.equals("N") || playerType.equals("S")) {
						String lobbyChoice = ViewTUI.readString(
								"Please fill in the lobby number you would like to enter: ");
						sendToGame("CONNECT " + name + " " + lobbyChoice);
					}
				} else if (splitMessage[0].equals(Protocol.SCORES)) {
					
					if (Integer.parseInt(splitMessage[1]) == playerNumber) {
						ViewTUI.staticPrint("You have won with ");
					} else {
						ViewTUI.staticPrint("You have lost with ");
					}
					ViewTUI.staticPrintline(splitMessage[1 + playerNumber] + " points");
					
					String playAgainChoice = ViewTUI.readString("Play again? true or false? ");
					sendToGame(Protocol.PLAY_AGAIN + " " + playAgainChoice);
				}
			}

		} catch (IOException e) {
			ViewTUI.staticPrintline(
					"ERROR: could not create a socket on " + addr + " and port " + port);
			System.exit(0);
		}
	}

	public void sendToGame(String message) {
		printWriter.println(message);
		printWriter.flush();
	}

	public static void main(String[] args) {
		Client c = new Client();
		c.joinServer(args);
	}

	public InetAddress getIp(String host) {
		InetAddress addr = null;
		try {
			addr = InetAddress.getByName(host);
		} catch (UnknownHostException e) {
			return null;
		}
		return addr;
	}

	public int getPort(String portstr) {
		int port = 0;
		try {
			port = Integer.parseInt(portstr);
		} catch (NumberFormatException e) {
			return 0;
		}
		return port;
	}

	public String makeMove() {
		String move = null;
		// We are the first player
		if (turnCounter == 1) {
			move = player.determineFirstNetworkMove();
		} else {
			move = player.determineNetworkMove();
		}
		return move;
	}

	public void newGameRings(int numberOfPlayers, int playerNr) {
		int ringsPerSize = 3;

		if (numberOfPlayers == 2) {
			if (playerNr == 1) {
				// Adding the colors of the player
				playerColors.add(1);
				playerColors.add(3);
			} else if (playerNr == 2) {
				playerColors.add(2);
				playerColors.add(4);
			}

			// The number of different colors
			for (int i = 0; i < playerColors.size(); i++) {
				// The different sizes of rings
				for (int j = 0; j < 5; j++) {
					for (int k = 0; k < ringsPerSize; k++) {
						// For Bases
						if (j == 0) {
							playerRings.add(new Ring(j, playerNumber, playerColors.get(i), false));
						} else {
							playerRings.add(new Ring(j, playerNumber, playerColors.get(i), true));
						}

					}
				}
			}
		} else if (numberOfPlayers == 3) { // For a 3 player game
			if (playerNumber == 1) {
				playerColors.add(1);
			} else if (playerNumber == 2) {
				playerColors.add(2);
			} else {
				playerColors.add(3);
			}
			playerColors.add(4);

			int mainPlayerColorIndex = 0;
			int thirdColorIndex = 0;
			// For the full color
			for (int j = 0; j < 5; j++) {
				for (int k = 0; k < 3; k++) {
					playerRings.add(new Ring(
							j, playerNumber, playerColors.get(mainPlayerColorIndex), true));
				}
			}

			// For the 1/3 color
			for (int i = 0; i < 5; i++) {
				if (i == 0) {
					playerRings.add(new Ring(
							i, playerNumber, playerColors.get(thirdColorIndex), false));
				}
			}
		} else if (numberOfPlayers == 4) { // For a 4 player game

			int colorIndex = 0;

			if (playerNumber == 1) {
				playerColors.add(1);
			} else if (playerNumber == 2) {
				playerColors.add(2);
			} else if (playerNumber == 3) {
				playerColors.add(3);
			} else if (playerNumber == 4) {
				playerColors.add(4);
			}

			for (int j = 0; j < 5; j++) {
				for (int k = 0; k < 3; k++) {
					playerRings.add(new Ring(j, playerNumber, playerColors.get(colorIndex), true));
				}
			}
		}
	}
	
	public void setHumanMove(String move) {
		attemptedMove = move;
	}
}
