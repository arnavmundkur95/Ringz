package tests;

import static org.junit.Assert.*;

import java.util.ArrayList;

import org.junit.Before;
import org.junit.Test;

import controllers.HumanPlayer;
import controllers.Player;
import models.Ring;
import views.ViewTUI;

/**
 * PlayerTest class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class PlayerTest {
	
	Player player;
	int playerNumber;
	String playerName;
	ArrayList<Integer> colors;
	ArrayList<Ring> rings;
	
	@Before
	public void setUp() throws Exception {
		playerNumber = 1;
		playerName = "Bob";
		colors = new ArrayList<>();
		rings = new ArrayList<>();
		player = new HumanPlayer(playerNumber, playerName);
	}

	@Test
	public void testGetPlayerName() {
		assertTrue(player.getPlayerName().equals(playerName));
	}
	
	@Test
	public void testGetPlayerNumber() {
		assertTrue(player.getPlayerNumber() == playerNumber);
	}
	
	@Test
	public void testGetPlayerColors() {
		colors.add(2);
		player.setColors(colors);
		
		assertTrue(player.getPlayerColors().size() == 1);
		assertTrue(player.getPlayerColors().get(0) == 2);
	}
	
	@Test
	public void testGetRings() {
		int color = 3;
		int size = 2;
		rings.add(new Ring(size, playerNumber, color, true));
		player.setRings(rings);
		
		assertTrue(player.getPlayerRings().get(0).getColor() == color
				&& player.getPlayerRings().get(0).getSize() == size);
	}
	
	@Test 
	public void testAddStartBase() {
		player.addStartBase();
		
		ArrayList<Ring> temp = player.getPlayerRings();
		
		assertTrue(temp.size() == 1);
		assertTrue(temp.get(0).getColor() == 0 &&
				temp.get(0).getSize() == 0);
	}
	
	@Test
	public void testClearColors() {
		for (int i = 0; i < 2; i++) {
			colors.add(i + 1);
		}
		
		player.setColors(colors);
		
		assertTrue(player.getPlayerColors().size() != 0);
		
		player.clearColors();
		
		assertTrue(player.getPlayerColors().size() == 0);
	}
	
	@Test 
	public void testClearRings() {
		int color = 2;
		
		for (int i = 0; i < 3; i++) {
			rings.add(new Ring(i, playerNumber, color, true));
		}
		
		player.setRings(rings);
		
		assertTrue(player.getPlayerRings().size() != 0);
		
		player.clearRings();
		
		assertTrue(player.getPlayerRings().size() == 0);
	}
	
	@Test
	public void testDisplayRings() {
		int color = 2;
		for (int i = 0; i < 3; i++) {
			rings.add(new Ring(i, playerNumber, color, true));
		}
		colors.add(color);
		player.setColors(colors);
		player.setRings(rings);
		
		ViewTUI.staticPrintline(player.displayRings());
		assertTrue(player.displayRings().length() != 0);
	}
	
	@Test
	public void testUpdateRingList() {
		int color = 2;
		int size = 2;
		colors.add(color);
		for (int i = 0; i < 3; i++) {
			rings.add(new Ring(i, playerNumber, color, true));
		}
		
		player.setColors(colors);
		player.setRings(rings);
		
		player.updateRingList(color, size);
		
		assertTrue(!player.getPlayerRings().contains(new Ring(size, playerNumber, color, true)));
	}
}
