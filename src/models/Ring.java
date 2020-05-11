package models;

/**
 * Ring class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class Ring {
	private int size;
	private boolean worthPoints;
	private int belongsToPlayer;
	private int color;
	
	public Ring(int size, int belongsToPlayer, int color, boolean worthPoints) {
		this.size = size;
		this.belongsToPlayer = belongsToPlayer;
		this.worthPoints = worthPoints;
		this.color = color;
	}
	
	public int getSize() {
		return size;
	}
	
	public boolean getWorthPoints() {
		return worthPoints;
	}
	
	public int getBelongsToPlayer() {
		return belongsToPlayer;
	}
	
	public int getColor() {
		return color;
	}
	
	public String toString() {
		return "Size: " + size + " and color: " + color;
	}
}
