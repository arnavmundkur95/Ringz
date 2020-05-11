package tests;

import java.util.ArrayList;

import controllers.LocalGame;
import views.ViewTUI;

/**
 * OfflineGameTest class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class OfflineGameTest {
	
	private static int amountOfPlayers;
	// At most 4 players, at least 2 player
	private static int humanAmount = 2;
	private static int computerAmount = 2;
	
	public static void main(String[] args) {
		amountOfPlayers = humanAmount + computerAmount;
		ArrayList<String> names = new ArrayList<>();
		char[] typesOfPlayers = new char[amountOfPlayers];
		
		
		if ((humanAmount + computerAmount) > 4 || (humanAmount + computerAmount) < 2) {
			ViewTUI.staticPrintline("Player count does not add up");
			System.exit(-1);
		}
		
		for (int i = 0; i < humanAmount; i++) {
			typesOfPlayers[i] = 'H';
			names.add("" + (int) (Math.random() * 100));
		}
		
		for (int i = humanAmount; i < computerAmount + humanAmount; i++) {
			typesOfPlayers[i] = 'N';
			names.add("" + (int) (Math.random() * 100));
		}
		
		new LocalGame(amountOfPlayers, typesOfPlayers, names); // Start the game
	}
}
