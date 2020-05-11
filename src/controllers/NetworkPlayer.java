package controllers;

import models.Board;
import views.ViewTUI;

/**
 * NetworkPlayer class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class NetworkPlayer extends Player {
	
	private ServerThread serverThread;
	
	public NetworkPlayer(int playerNumber, String name, ServerThread handler) {
		super(playerNumber, name);
		this.serverThread = handler;
	}

	// -- Commands ---------------------------------------------------

	public int validate(int lowerBound, int upperBound, String variable) {
		int answer = ViewTUI.readInt("Input the " + variable + ": ");
		boolean invalid = answer < lowerBound || answer > upperBound;
		while (invalid) {
			ViewTUI.staticPrint("ERROR: " + variable + ": " + answer);
			ViewTUI.staticPrintline(" is not a valid choice.");
			answer = ViewTUI.readInt("Input the " + variable);
			invalid = answer < lowerBound || answer > upperBound;
		}
		return answer;
	}

	public void validateBoolean(int value, int lowerBound, int upperBound, String variable) {
		boolean invalid = value < lowerBound || value > upperBound;
		@SuppressWarnings("unused")
		String input = null;
		if (invalid) {
			ViewTUI.staticPrint("ERROR: " + variable + ": " + value);
			ViewTUI.staticPrintline(" is not a valid choice.");
			input = ViewTUI.readString("Input your choice like this: MOVE color size X Y ");
		}
	}

	public String determineFirstMove() {
		serverThread.sendMessage("> " + getPlayerName() + " place Start base 1 <=  X,Y <= 3 ");
		String move = serverThread.getMove();
		serverThread.resetMove();
		return move;
	}

	/**
	 * Asks the user to input the field where to place the next mark. This is done
	 * using the standard input/output.
	 * 
	 * @param board
	 *            the game board
	 * @return the player's chosen field
	 */
	public String determineMove(Board board) {
		serverThread.sendMessage("> " + getPlayerName());
		serverThread.sendMessage("Input your choice like this: MOVE color size X Y ");
		
		String move = serverThread.getMove();
		serverThread.resetMove();
		return move;
	}

	
	public String determineNetworkMove() {
		serverThread.sendMessage("> " + getPlayerName());
		serverThread.sendMessage("Input your choice like this: MOVE color size X Y ");
		@SuppressWarnings("unused")
		String move = serverThread.getMove();
		serverThread.resetMove();
		return null;
		
	}

	public String determineFirstNetworkMove() {
		return null;		
	}

	@Override
	public String determineNetworkMove(Board board) {
		return null;
	}

	@Override
	public String makeMoveWithBoard(int turnCounter, Board board) {
		return null;
	}
}
