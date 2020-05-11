package controllers;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Random;

import models.Board;
import models.Ring;

/**
 * ComputerPlayer class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class ComputerPlayer extends Player {

	private PrintWriter writer;
	
	public ComputerPlayer(int playerNumber, String name) {
		super(playerNumber, name + " Computer Player");
	}
	
	public ComputerPlayer(int playerNumber, String name, PrintWriter p) {
		super(playerNumber, name);
		writer = p;
	}
	
	@Override
	public String determineFirstMove() {
		String input = "MOVE 0 0 ";
		Random random = new Random();
		int lowerBound = 1;
		int upperBound = 3;
		int x = random.nextInt(upperBound - lowerBound) + lowerBound;
		input += x + " ";
		int y = random.nextInt(upperBound - lowerBound) + lowerBound;		
		input += y + " ";
		return input;
	}

	@Override
	public String determineMove(Board board) {
		ArrayList<String> availableMoves = board.availableMoves(this);
		int item = new Random().nextInt(availableMoves.size()); // random index in our moves
		String chosenMove = availableMoves.get(item);
		String[] values = chosenMove.split(" ");
		
		String ringToFind = chosenMove.substring(0, 1);
		boolean moveFound = false;
		do {
			for (int i = 0; i < rings.size(); i++) {
				// Found a ring with that size	
				String ring = Integer.toString(rings.get(i).getSize());
				if (ring.equals(ringToFind)) {
					String output = "MOVE ";
					int color = rings.get(i).getColor();
					output += color + " ";
					int size = Character.getNumericValue(values[0].charAt(0));
					output += size + " ";
					int x = Character.getNumericValue(values[1].charAt(0));
					output += x + " ";
					int y = Character.getNumericValue(values[2].charAt(0));
					output += y + " ";
					moveFound = true;
					return output;
				}
			}
		} while (!moveFound);
		return null;
	}
	
	public String determineFirstNetworkMove() {
		String input = "MOVE 0 0 ";
		Random random = new Random();
		int lowerBound = 1;
		int upperBound = 3;
		int x = random.nextInt(upperBound - lowerBound) + lowerBound;
		input += x + " ";
		int y = random.nextInt(upperBound - lowerBound) + lowerBound;		
		input += y;
		sendMove(input);
		return input;
	}

	public void sendMove(String message) {
		writer.println(message);
		writer.flush();
	}

	public String determineNetworkMove(Board board) {
		ArrayList<String> availableMoves = board.availableMoves(this);
		int randomAvailableMove; // random index in our available moves
		int randomAvailableRing;
		Ring randomRing;
		String chosenMove;
		String[] values;
		String output = "";
		String ringToFind; 
		boolean moveFound = false;
		String ringSize;
		do {
			randomAvailableMove = new Random().nextInt(availableMoves.size());
			chosenMove = availableMoves.get(randomAvailableMove);
			values = chosenMove.split(" ");
			
			ringToFind = chosenMove.substring(0, 1); // Size of the ring which we will use
			
			randomAvailableRing = new Random().nextInt(rings.size());
			randomRing = rings.get(randomAvailableRing);
		
			ringSize = Integer.toString(randomRing.getSize());
			
			// Found a ring with that size	
			if (ringSize.equals(ringToFind)) {
				output = "MOVE ";
				int color = randomRing.getColor();
				output += color + " ";
				int size = Integer.parseInt(ringSize);
				output += size + " ";
				int x = Character.getNumericValue(values[1].charAt(0));
				output += x + " ";
				int y = Character.getNumericValue(values[2].charAt(0));
				output += y + " ";
				moveFound = true;
				break;
			}
		} while (!moveFound);

		sendMove(output);
		return output;		
	}

	public String makeMoveWithBoard(int turn, Board b) {
		String string = null;
		if (turn == 1) {
			string = determineFirstNetworkMove();
		} else {
			string = determineNetworkMove(b);
		}
		return string;
	}

	@Override
	public String determineNetworkMove() {
		return null;
	}
}
