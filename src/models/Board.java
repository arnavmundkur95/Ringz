package models;

import java.util.ArrayList;

import controllers.Player;

/**
 * Board class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class Board {
	// ------------------ Instance variables ----------------
	public static final int DIM = 5; // Dimension of the board
	private Node[] nodes = new Node[25];
	private int[] pointsForPlayers;
	/*@ private invariant playerCount <= 4 & playerCount >= 2; */
	private int playerCount;
	
	// -- Constructor -----------------------------------------------
	/**
	 * Creates an empty Board with empty Nodes.
	 */
	/*@ requires playerAmount >= 2 && playerAmount <= 4;
	//@ ensures getPlayerPoints() != null && 
	  (\forall int index; index <= DIM * DIM
	 & index >= 0; getNode(index) != null); */
	public Board(int playerAmount) {
		
		assert playerAmount >= 2 && playerAmount <= 4;
		
		playerCount = playerAmount;
		pointsForPlayers = new int[playerCount];
		for (int i = 0; i < nodes.length; i++) {
			int[] rowCol = index(i);
			nodes[i] = new Node(rowCol[0], rowCol[1]);
		}
		reset();
	}
	
	 // ------------------ Queries --------------------------	
	/**
	 * Reset the board.
	 */
	/*@ ensures (\forall int i; 0 <= i & i < DIM * DIM; getPlayerPoints()[i] == 0);
	 */
	public void reset() {
		for (int i = 0; i < pointsForPlayers.length; i++) {
			pointsForPlayers[i] = 0;
		}
		for (int i = 0; i < nodes.length; i++) {
			nodes[i].resetNode();
		}
	}
	
	/**
	 * Calculates the index in the linear array of fields from a (row, col)
	 * pair.
	 * 
	 * @return the index belonging to the (row,col)-field
	 */
	//@ requires 0 <= row & row < getDimension();
	//@ requires 0 <= col & col < getDimension();
	/*@ pure */
	public int index(int row, int col) {
		return (getDimension() * row) + col;
	}

	/**
	 * Returns String of row and column from an index.
	 * 
	 * @param index
	 * @return row and column
	 */
	//@ requires index >= 0 && index <= 24;
	/*@ pure */
	public int[] index(int index) {
		int[] answer = new int[2];
		int row = index / DIM;
		answer[0] = row;
		int col = index % DIM;
		answer[1] = col;
		return answer;
	}

	/**
	 * Returns true if index is valid and the size is valid.
	 * 
	 * @return true if 0 <= index < DIM*DIM
	 */
	//@ requires index >= 0 && index <= 24;
	//@ ensures \result == (0 <= index && index < getDimension() * getDimension());
	/*@pure */
	public boolean isNode(int index) {
		if (index < (DIM * DIM)) {
			return true;
		}
		return false;
	}

	/**
	 * Returns true if index is valid and the size is valid.
	 *
	 * @return true if 0 <= row < DIM && 0 <= col < DIM
	 */
	//@ requires 0 <= row & row < getDimension();
	//@ requires 0 <= col & col < getDimension();
	//@ ensures \result == (0 <= row && row < getDimension() && 0 <= col && col < getDimension());
	/*@pure */
	public boolean isNode(int row, int col) {
		if (row < DIM && col < DIM) {
			return true;
		}
		return false;
	}

	/**
	 * Returns the content of the Node i.
	 *
	 * @param i index of the Node
	 * @return the Node
	 */
	//@ requires i >= 0 && i <= 24;
	/*@ pure */
	public Node getNode(int i) {
		if (isNode(i)) {
			return nodes[i];
		}
		return null;
	}

	/**
	 * Returns the content of the node referred to by the (row,col) pair.
	 *
	 * @param row
	 *            the row of the node
	 * @param col
	 *            the column of the node
	 * @return the mark on the field
	 */
	//@ requires 0 <= row & row < getDimension();
	//@ requires 0 <= col & col < getDimension();
	//@ ensures true;
	/*@pure */
	public Node getNode(int row, int col) {
		if (isNode(row, col)) {
			return nodes[index(row, col)];
		}
		return null;
	}

	/**
	 * Returns true if the ring size i is empty.
	 *
	 * @param i
	 *            the index of the Node
	 * @return true if the ring size is empty
	 */
	
	//@ requires i >= 0 && i <= 24;
	/*@ pure */
	public boolean isFullNode(int i) {
		if (isNode(i) && nodes[i].isEmptyRing(i)) {
			return true;
		}
		return false;
	}

	/**
	 * Returns true if the field i is empty.
	 *
	 * @param row
	 *            the row of the field
	 * @param col
	 *            the column of the field
	 * @return true if the field is empty
	 */
	//@ requires 0 <= row & row < getDimension();
	//@ requires 0 <= col & col < getDimension();
	/*@ pure */
	public boolean isFullNode(int row, int col) {
		return nodes[index(row, col)].isFull();
	}

	/**
	 * Method for receiving playersPoints.
	 * @return
	 */
	/*@ pure */
	public int[] getPlayerPoints() {
		return pointsForPlayers;
	}

	/**
	 * Returns the numbers of players if the game has a winner. 
	 * If multiple people have the same amount of points, then letters are concatenated.
	 * If there is one letter then a player has a bigger score than all the other players.
	 *
	 * @return String winner playerNumbers.
	 */
	/*@ ensures \result != null; */
	public String checkForWinner() {
		int score;
		String winnerNumber = ""; // The number of the player who won

		int nodeWinner;
		// Loop through all of the nodes and check if they have a winner
		for (int n = 0; n < nodes.length; n++) {
			nodeWinner = nodes[n].getWonNode();
			// Someone won this node
			if (nodeWinner != -1) {
				pointsForPlayers[nodeWinner] = pointsForPlayers[nodeWinner] + 1;
			}
		}

		// Calculate the player with most points
		int max = 0; // Max score of all the players in the game

		// Find the maximum score
		for (int points : pointsForPlayers) {
			if (points > max) {
				max = points;
			}
		}

		// Loop through all of the scores and check who has max
		for (int i = 0; i < pointsForPlayers.length; i++) {
			score = pointsForPlayers[i];
			if (score == max) {
				winnerNumber += i;
			}
		}

		return winnerNumber;
	}


	/**
	 * Method for checking if any player has won any Nodes.
	 */
	public void calculatePoints() {
		int[] pointsOnNode = new int[playerCount];

		// Loop through the nodes
		for (Node node : nodes) {
			for (int i = 0; i < pointsOnNode.length; i++) {
				pointsOnNode[i] = 0;
			}

			// Node has no rings
			if (node.isEmptyNode()) {
				continue;
			}

			// Loop through all rings
			int playerNumber;
			for (int r = 0; r < node.getRingsOnNode().length; r++) {
				Ring ring = node.getRingsOnNode()[r];
				if (ring == null || !ring.getWorthPoints()) {
					continue;
				} else if (ring.getSize() == 0) {
					break;
				}

				// Find player
				playerNumber = ring.getBelongsToPlayer();
				pointsOnNode[playerNumber] += 1;
			}

			int maximumScore = 0; // Max score of all the players on this node
			int score; // Score of each player
			int winnerNumber = -1; // The number of the player who won
			boolean maxFound = false;

			// Loop through all the player scores
			for (int i = 0; i < pointsOnNode.length; i++) {
				score = pointsOnNode[i];
				if (score == maximumScore) {
					maxFound = false;
					winnerNumber = -1;
				} else if (score > maximumScore) {
					maximumScore = score;
					maxFound = true;
					winnerNumber = i;
				}
			}

			// There is a winner
			if (maxFound) {
				node.setWonNode(winnerNumber);
			}
		}
	}

	
	/**
	 * Method for receiving the DIM (Dimension).
	 * @return
	 */
	/*@ pure */
	public int getDimension() {
		return DIM;
	}

	/**
	 * Returns a String representation of thw board. In addition to the current situation,
	 * the String also shows the numbering in the correct spaces with letters assigned to numbers.
	 *
	 * @return the game situation as String
	 */
	/*@ pure */
	public String toString() {
		String string = "";
		string += "\t\t\t     Y\n\n\t";
		for (int i = 0; i < DIM; i++) {
			string += "   " + i + "     ";
		}

		// Printing all of the nodes toString()
		for (int i = 0; i < nodes.length; i++) {
			if (i % DIM == 0) {
				string += "\n\n";
				if (i == 10) {
					string += "X" + "    " + i / 5 + "  ";
				} else {
					string += "     " + i / 5 + "  ";
				}
			}
			string += nicerDisplay(nodes[i].toString()) + "  ";
		}
		return string;
	}
	
	/**
	 * Method for making a letter out of the number that was made into a char.
	 * @param c char we would like to change
	 * @return the character that will be used on the board
	 */
	//@ requires c != '\u0000';
	/*@ pure */
	public char convertNumToChar(char c) {
		char letter = 0;
		switch (c) {
			case '0' :
				letter = 'o';
				break;
			case '1' :
				letter = 'a';
				break;
			case '2' :
				letter = 'b';
				break;
			case '3' :
				letter = 'c';
				break;
			case '4' :
				letter = 'd';
				break;
			case '7' :
				letter = '#';
				break;
			case '8' :
				letter = '-';
				break;
			case '9' :
				letter = '+';
				break;
		}
		return letter;
	}
	
	//@ requires string != null;
	/*@ pure */
	public String nicerDisplay(String string) {
		String output = "";
		char[] numbers = string.toCharArray();

		for (int i = 0; i < numbers.length; i++) {
			output += convertNumToChar(numbers[i]);
		}
		return output;
	}

	/**
	 * Function loops through all the nodes on the board to look for empty
	 * spaces in each node and adds the size of ring, and the row and column of
	 * the node to the arraylist of available moves.
	 * 
	 * @return availableMoves ArrayList of Strings of available moves
	 */
	//@ requires player != null;
	/*@ pure */
	public ArrayList<String> availableMoves(Player player) {

		// colors and rings
		ArrayList<String> availableMoves = new ArrayList<>();
		ArrayList<Node> playableNodes = new ArrayList<>();
		ArrayList<Integer> playerColors = player.getPlayerColors();

		for (int j = 0; j < playerColors.size(); j++) {
			for (int i = 0; i < nodes.length; i++) {
				int[] tocheck = nodes[i].getVisualRings();
				for (int k = 0; k < tocheck.length; k++) {
					// checking each ring on each node for a match with color
					if (!playableNodes.contains(nodes[i])
							&& (tocheck[k] == playerColors.get(j)
									|| tocheck[k] == 0)) {
						playableNodes.add(nodes[i]);
					}
				}
			}
		}

		int looplength = playableNodes.size();
		// looping through playableNodes to find nodes above, below, left and right
		for (int i = 0; i < looplength; i++) {
			int col = playableNodes.get(i).getCol();
			int row = playableNodes.get(i).getRow();
			int index = index(row, col);

			// checking row above
			int up = index - DIM;
			if (up >= 0 && up < 25) {
				playableNodes.add(nodes[up]);
			}

			// checking below
			int down = index + DIM;
			if (down >= 0 && down < 25) {
				playableNodes.add(nodes[down]);
			}

			// checking left
			int left = index - 1;
			if (left >= 0 && left < 25) {
				playableNodes.add(nodes[left]);
			}

			// checking right
			int right = index + 1;
			if (right >= 0 && right < 25) {
				playableNodes.add(nodes[right]);
			}
		}

		ArrayList<Ring> playersRings = player.getPlayerRings();

		for (int n = 0; n < playableNodes.size(); n++) {

			int col = playableNodes.get(n).getCol();
			int row = playableNodes.get(n).getRow();
			int index = index(row, col);

			if (playableNodes.get(n).isEmptyNode()) {

				// checking row above
				int up = index - DIM;
				boolean canPlaceBase = true;

				if ((up >= 0 && up < 25) && nodes[up].hasBase()) {
					canPlaceBase = false;
				}

				// checking below
				int down = index + DIM;
				if (down >= 0 && down < 25 && nodes[down].hasBase()) {
					canPlaceBase = false;
				}

				// checking left
				int left = index - 1;
				if (left >= 0 && left < 25 && nodes[left].hasBase()) {
					canPlaceBase = false;
				}

				// checking right
				int right = index + 1;
				if (right >= 0 && right < 25 && nodes[right].hasBase()) {
					canPlaceBase = false;
				}

				for (Ring r : playersRings) {
					if (canPlaceBase && r.getSize() == 0) {
						availableMoves.add("0 " + playableNodes.get(n).getRow()
								+ " " + playableNodes.get(n).getCol());
					}
				}
			}

			int[] ringsOnNode = playableNodes.get(n).getVisualRings();
			for (int i = 0; i <= (ringsOnNode.length / 2); i++) {
				if ((ringsOnNode[i] == 8
						&& (ringsOnNode[ringsOnNode.length - 1 - i]) == 8)
						|| ringsOnNode[i] == 9) {
					for (Ring r : playersRings) {
						if (r.getSize() == (4 - i)) {
							availableMoves.add((4 - i) + " "
									+ playableNodes.get(n).getRow() + " "
									+ playableNodes.get(n).getCol());
						}
					}
				}
			}
		}
		return availableMoves;
	}
	
	/**
	 * A simple getter for the playerCount.
	 * 
	 * @return playerCount The number of players in the game.
	 */
	//*@ ensures \result <= 2 && \result >= 4; 
	public int getPlayerCount() {
		return playerCount;
	}
}
