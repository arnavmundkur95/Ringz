package models;

/**
 * Node class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class Node {

	public static final int MAX_RINGS_ON_NODE = 4;
	public static final int[] COLORS = {0, 1, 2, 3, 4};
	public boolean[] colorWorth = new boolean[COLORS.length];

	private int wonNode; // Player that occupied a teritory
	private int[] ringsOnNode = {8, 8, 8, 9, 8, 8, 8};
	private int row;
	private int col;

	private Ring[] rings;

	/**
	 * Creates a new Node at the row and col specified.
	 * 
	 * @param row
	 *            Row of the particular Node.
	 * @param col
	 *            Col of the particular Node.
	 */
	public Node(int row, int col) {
		this.row = row;
		this.col = col;
		assert this.row == row;
		assert this.col == col;
		rings = new Ring[MAX_RINGS_ON_NODE + 1];
		resetNode();
	}

	public int getRow() {
		return row;
	}

	public int getCol() {
		return col;
	}

	public int getWonNode() {
		return wonNode;
	}

	public void setWonNode(int playerNumber) {
		this.wonNode = playerNumber;
	}

	/**
	 * Resets a Node by clearing out all the rings.
	 */
	public void resetNode() {
		wonNode = -1;
		for (int i = 0; i < ringsOnNode.length; i++) {
			if (i == 3) {
				ringsOnNode[i] = 9;
			} else {
				ringsOnNode[i] = 8;
			}
		}
		for (int r = 0; r < rings.length; r++) {
			rings[r] = null;
		}
	}

	public boolean hasBase() {
		return ringsOnNode[0] == 7;
	}

	/**
	 * Places a ring of a particular color and size on a Node.
	 * 
	 * @param color
	 *            The color of the ring being placed on the Node.
	 * @param size
	 *            The size of the ring being placed on the Node.
	 */

	public void setRing(int color, int size, Ring r) {
		// Rings size 1 - 4
		if (!isFull() && isEmptyRing(size)) {
			if (size == 1) {
				ringsOnNode[3] = color;
				rings[1] = r;

			} else if (size == 2) {
				ringsOnNode[2] = color;
				ringsOnNode[4] = color;
				rings[2] = r;

			} else if (size == 3) {
				ringsOnNode[1] = color;
				ringsOnNode[5] = color;
				rings[3] = r;

			} else if (size == 4) {
				ringsOnNode[0] = color;
				ringsOnNode[6] = color;
				rings[4] = r;
			}
		} else if ((isEmptyNode() && size == 0) && (r.getColor() != 0)) { // Rings of base size
			for (int i = 0; i < ringsOnNode.length; i++) {
				if (i == 0 || i == 6) {
					ringsOnNode[i] = 7;
				} else {
					ringsOnNode[i] = color;
				}
			} 
			rings[0] = r;
		} else if ((isEmptyNode() && size == 0) && r.getColor() == 0) { // Rings of starting base

			for (int i = 0; i < ringsOnNode.length; i++) {
				ringsOnNode[i] = 0;
			}
			rings[0] = r;
		}
	}

	/**
	 * 
	 * @return true If the Node is full.
	 */
	public boolean isFull() {
		for (int c : ringsOnNode) {
			if (c == 9 || c == 8) {
				return false;
			}
		}
		return true;
	}

	/**
	 * @param size
	 *            Size of the ring being checked for on the Node.
	 * @return true If the ring size specified in the param is not occupied by
	 *         another ring on the particular Node i.e is '+' or '-'.
	 */
	public boolean isEmptyRing(int size) {
		if (size == 1 && ringsOnNode[3] == 9) {
			return true;
		} else if (size == 2 && ringsOnNode[2] == 8) {
			return true;
		} else if (size == 3 && ringsOnNode[1] == 8) {
			return true;
		} else if (size == 4 && ringsOnNode[0] == 8) {
			return true;
		}
		return false;
	}

	/**
	 * 
	 * @return false If the Node has rings on it.
	 * @return true If the Node does not have rings on it.
	 */
	public boolean isEmptyNode() {
		int[] emptyCheck = {8, 8, 8, 9, 8, 8, 8};
		for (int i = 0; i < emptyCheck.length; i++) {
			if (emptyCheck[i] != ringsOnNode[i]) {
				return false;
			}
		}
		return true;
	}

	public boolean[] giveColorWorth() {
		return colorWorth;
	}

	public int[] getVisualRings() {
		return ringsOnNode;
	}

	/**
	 * Returns an array of the Rings on the Node.
	 */

	public Ring[] getRingsOnNode() {
		return rings;
	}

	public String toString() {
		String string = "";
		for (int i = 0; i < ringsOnNode.length; i++) {
			string += Integer.toString(ringsOnNode[i]);
		}
		return string;
	}
}
