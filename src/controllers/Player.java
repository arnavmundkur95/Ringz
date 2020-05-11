package controllers;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;

import models.Board;
import models.Ring;
import views.ViewTUI;

/**
 * Player class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public abstract class Player {
	// ------------------ Instance variables ----------------
	private String name;
	protected ArrayList<Ring> rings;
	/*@ private invariant colors.contains(1) || colors.contains(2) ||
	  colors.contains(3) || colors.contains(4); */
	private ArrayList<Integer> colors;
	
	/*@ private invariant playerNumber >= 1 && playerNumber <= 4; */
	private int playerNumber;
	
	// -- Constructor -----------------------------------------------
	/**
	 * Creates a new player with a specified player number.
	 * @param playerNumber
	 */
	/*@ requires playerNumber >= 1 && playerNumber <= 4 && name != null; */
	/*@ ensures name == getPlayerName() && playerNumber == getPlayerNumber(); */
	public Player(int playerNumber, String name) {
		assert playerNumber >= 1 && playerNumber <= 4;
		assert name != null;
		
		this.playerNumber = playerNumber;
		this.name = name;
		rings = new ArrayList<Ring>();
		colors = new ArrayList<Integer>();
	}
	
	// -- Abstract Methods-------------------------------------------
	
	/**
	 * Determines the normal move to be played for a SinglePlayer game.
	 * @param board the current game board
	 * @return the player's choice
	 */
	/*@ requires board != null; */
	/*@ ensures \result != null; */
	public abstract String determineMove(Board board);
	
	/**
	 * Determines the first move to be played for a SinglePlayer game.
	 * @return the player's choice
	 */
	/*@ ensures \result != null; */
	public abstract String determineFirstMove();
	
	/**
	 * Determines the first move to be played for a MultiPlayer game.
	 * @return the player's choice
	 */
	/*@ ensures \result != null; */
	public abstract String determineFirstNetworkMove();
	
	/**
	 * Determines the first move to be played for a MultiPlayer game.
	 * @param board the current game board
	 * @return the player's choice
	 */
	/*@ requires board != null; */
	/*@ ensures \result != null; */
	public abstract String determineNetworkMove(Board board);
	
	/**
	 * Determines the first move to be played for a singlePlayer person.
	 * @return the player's choice
	 */
	/*@ ensures \result != null; */
	public abstract String determineNetworkMove();
	
	/**
	 * Method for getting input from the user for a move.
	 * @param turnCounter Current turn
	 * @param board Board of the Servers game
	 * @return the players move
	 */
	/*@ requires turnCounter >= 0 && board != null; */
	/*@ ensures \result != null; */
	public abstract String makeMoveWithBoard(int turnCounter, Board board);
	
	// --Commands-------------------------------------------
	/**
	 * Returns the array of unused rings a player has.
	 * @return rings Array of unused rings.
	 */
	/*@ requires color >= 0 && color <= 4 && size >= 0 && size <= 4 && 
	 getPlayerColors().contains(color) && getPlayerRings().contains(size); */
	public Ring updateRingList(int color, int size) {
		for (int i = 0; i < rings.size(); i++) {
			if (rings.get(i).getColor() == color && rings.get(i).getSize() == size) {
				Ring temp = rings.get(i);
				rings.remove(rings.get(i));
				return temp;
			}
		}
		return null;
	}
	
    /**
     * Makes a move on the board and remove the ring the player has played.
     * @param board the current board
     * @param move the move of the player
     */
    /*@ requires move != null && board != null; */
	/*@ ensures \result != null; */
    public Board makeBoardMove(String move, Board board) {
    	ViewTUI.staticPrintline(move);
    	String[] commands = move.split(" ");
    	int[] values = new int[commands.length - 1];
    	
    	for (int i = 0; i < values.length; i++) {
    		values[i] = Integer.parseInt(commands[i + 1]);
    	}
        Ring r = updateRingList(values[0], values[1]);
        board.getNode(values[2], values[3]).setRing(values[0], values[1], r);
        return board;
    }
    
    /**
     * Makes a move on the board and make a new ring which is put on the board.
     * @param move the move of the player
     * @param board the current board
     * @param belongsToPlayer the player number of who this ring belongs to
     */
    /*@ requires move != null && board != null; */
	/*@ ensures \result != null; */
    public Board makeEnemyMove(String move, Board board, int belongsToPlayer) {
    	String[] commands = move.split(" ");
    	int[] values = new int[commands.length - 1];
    	
    	for (int i = 0; i < values.length; i++) {
    		values[i] = Integer.parseInt(commands[i + 1]);
    	}
        Ring r = new Ring(values[1], belongsToPlayer, values[0], false);
        board.getNode(values[2], values[3]).setRing(values[0], values[1], r);
        return board;
    }
    
	/**
	 * Give a certain player all the rings it may use during the game.
	 */
    /*@ requires rings != null;*/
	public void setRings(ArrayList<Ring> rings) {
		this.rings.addAll(rings);
	}
	
	/**
	 * Give a certain player all the colors it may use during the game.
	 */
	/*@ requires colors != null; */
	public void setColors(ArrayList<Integer> colors) {
		this.colors = colors;
	}
	
	/**
	 * Method that adds the start base to the player who starts the game.
	 */
	/*@ ensures getPlayerRings().size() != 0; */
	public void addStartBase() {
		rings.add(new Ring(0, 0, 0, false));
	}
	/**
	 * Method for reseting the players rings.
	 */
	/*@ ensures getPlayerRings().size() == 0; */
	public void clearRings() {
		this.rings = new ArrayList<>();
	}
	
	/**
	 * Method for reseting the players colors.
	 */
	/*@ ensures getPlayerColors().size() == 0; */
	public void clearColors() {
		this.colors = new ArrayList<>();
	}

	/**
	 * Returns the array of unused rings a player has in a nice and cleanly structured way.
	 * Example: Color 1 [2,3,4]
	 * @return rings Array of unused rings.
	 */
	/*@ ensures (getPlayerRings().size() != 0) ==> (\result != null); */
	public String displayRings() {
		String color = "Color: ";
		String size = "Size: ";
		String[] string = rings.toString().split(",");
		int playerColors = colors.size();
		ArrayList<ArrayList<Integer>> cols = new ArrayList<>();
		
		while (cols.size() < playerColors) {
			cols.add(new ArrayList<>());
		}
		
		HashMap<String, ArrayList<Integer>> answer = new HashMap<>();
		
		for (int i = 0; i  < colors.size(); i++) {
			answer.put(colors.get(i).toString(), new ArrayList<Integer>());
		}
		
		for (int i = 0; i < string.length; i++) {
			int index = string[i].indexOf(size);
			int tempsize = Character.getNumericValue(string[i].charAt(index + 6));
			int colorIndex = string[i].indexOf(color);
			int tempcolor = Character.getNumericValue(string[i].charAt(colorIndex + 7));
			answer.get(Integer.toString(tempcolor)).add(tempsize);
		}
		
		@SuppressWarnings("rawtypes")
		Set keys = answer.keySet();
		@SuppressWarnings("rawtypes")
		Iterator i = keys.iterator();
		String giveBack = "";
		while (i.hasNext()) {
			String key = (String) i.next();
			ArrayList<Integer> value = answer.get(key);
			giveBack = giveBack + ("\n" + "Color " + key + ": " + value + "\n");
		}
		return giveBack;
	}
	
	/**
	 * Returns the array of unused rings a player has.
	 * @return rings Array of unused rings.
	 */
	/*@ pure */
	public ArrayList<Ring> getPlayerRings() {
		return rings;
	}
	
	/**
	 * Returns the player's number.
	 * 
	 * @return playerNumber The number of the player.
	 */
	/*@ ensures \result >= 1 && \result <= 4; */
	/*@ pure */
	public int getPlayerNumber() {
		return playerNumber;
	}

	/**
	 * Returns the player's name.
	 * 
	 * @return playerName The name of the player.
	 */
	/*@ pure */
	public String getPlayerName() {
		return name;
	}
	
	/**
	 * Returns the player's colors.
	 * 
	 * @return points The number of colors the player has.
	 */
	/*@ ensures \result != null; */
	/*@ pure */
	public ArrayList<Integer> getPlayerColors() {
		return colors;
	}
}
