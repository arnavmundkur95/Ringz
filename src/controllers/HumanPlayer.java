package controllers;

import models.Board;
import views.ViewTUI;

/**
 * HumanPlayer class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class HumanPlayer extends Player {

	String attemptedMove;
	public HumanPlayer(int playerNumber, String name) {
		super(playerNumber, name);
		attemptedMove = null;
	}

	// -- Commands ---------------------------------------------------

	public int validate(int lowerBound, int upperBound, String variable) {
		int answer = ViewTUI.readInt("Input the " + variable + ": ");
		boolean invalid = answer < lowerBound || answer > upperBound;
		while (invalid) {
			ViewTUI.staticPrint("ERROR: " + variable + ": ");
			ViewTUI.staticPrintline(answer + " is not a valid choice.");
			answer = ViewTUI.readInt("Input the " + variable);
			invalid = answer < lowerBound || answer > upperBound;
		}
		return answer;
	}

	public void validateBoolean(int value, int lowerBound, int upperBound, String variable) {
		boolean invalid = value < lowerBound || value > upperBound;
		@SuppressWarnings("unused")
		String input;
		if (invalid) {
			ViewTUI.staticPrintline("ERROR: " + variable + ": ");
			ViewTUI.staticPrintline(value + " is not a valid choice.");
			input = ViewTUI.readString("Input your choice like this: MOVE color size X Y ");
		}
	}

	public String determineFirstMove() {
		ViewTUI.staticPrintline("> " + getPlayerName() + " place Start base X, Y between 1 and 3 ");
		String input = ViewTUI.readString("Input your choice like this: MOVE 0 0 X Y ");
		return input;
	}
	
	public String determineFirstNetworkMove() {
		ViewTUI.staticPrintline("> " + getPlayerName() + " place Start base X, Y between 1 and 3 ");
		ViewTUI.staticPrintline("Input your choice like this: MOVE 0 0 X Y ");
		return null;
	}
	
	public String determineNetworkMove() {
		ViewTUI.staticPrintline("> " + getPlayerName() + " place one of your rings ");
		ViewTUI.staticPrintline("Input your choice like this: MOVE Color Size X Y ");
		return null;
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
		ViewTUI.staticPrint("> " + getPlayerName());
		String input = ViewTUI.readString(" Input your choice like this: MOVE color size X Y ");
		return input;
	}

	public void makeMoveWithBoard(int turn) {
		if (turn == 1) {
			determineFirstNetworkMove();
		} else {
			determineNetworkMove();
		}
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
