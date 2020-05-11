package tests;

import static org.junit.Assert.*;

import java.util.ArrayList;

import org.junit.Before;
import org.junit.Test;

import controllers.HumanPlayer;
import controllers.Player;
import models.Board;
import models.Ring;
import views.ViewTUI;

/**
 * BoardTest class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class BoardTest {
	
	private Board board;
	int numberOfPlayers = 3;
	
	@Before
	public void setUp() {
		board = new Board(numberOfPlayers);	
	}

	@Test
	public void testSetUp() {
		assertTrue(board.getPlayerCount() == numberOfPlayers);
		assertTrue(board.getPlayerPoints().length == numberOfPlayers);
	}
	
	
	@SuppressWarnings("static-access")
	@Test
	public void testReset() {
		board.reset();
		int[] playerPoints = board.getPlayerPoints();
		
		for (int i = 0; i < playerPoints.length; i++) {
			assertTrue(playerPoints[i] == 0);
		}
		
		for (int i = 0; i < board.getDimension() * board.getDimension(); i++) {
			assertTrue(board.getNode(i).getWonNode() == -1);
			
			for (int j = 0; j < board.getNode(i).MAX_RINGS_ON_NODE; j++) {
				Ring[] rings = board.getNode(i).getRingsOnNode();
				for (int k = 0; k < rings.length; k++) {
					assertTrue(rings[k] == null);
				}
			}
		}
	}
	
	@Test
	public void testIndex2Arguments() {
		int testx = 3;
		int testy = 3;
		
		assertTrue(board.index(testx, testy) == 18);
	}
	
	@Test 
	public void testIndex1Argument() {
		@SuppressWarnings("unused")
		int testIndex = 18;
		int[] result = board.index(18);
		
		assertTrue(result[0] == 3 && result[1] == 3);
	}
	
	@Test
	public void testIsNode1Argument() {
		assertTrue(board.isNode(3));
		assertFalse(board.isNode(33));
	}
	
	@Test
	public void testIsNode2Arguments() {
		assertTrue(board.isNode(3, 3));
		assertFalse(board.isNode(3, 243));
	}
	
	@Test
	public void testGetNodeOneArgument() {
		
		assertTrue(board.getNode(4).getClass().toString().equals("class models.Node"));
	}
	
	@Test 
	public void testGetNodeTwoArguments() {
		assertTrue(board.getNode(2, 2).getClass().toString().equals("class models.Node"));
	}
	
	@Test
	public void testIsFullNode() {
		int testNodeIndex = 1;
		int testNodeX = 0;
		int testNodeY = 1;
		int testRingColor = 3;
		
		
		for (int i = 0; i < 5; i++) {
			Ring r = new Ring(i, 0, testRingColor, false);
			board.getNode(1).setRing(testRingColor, i, r);
		}
		
		assertTrue(board.getNode(testNodeIndex).isFull());
		assertTrue(board.getNode(testNodeX, testNodeY).isFull());	
	}
	
	@Test
	public void testAvailableMoves() {
		int playerNumber = 1;
		Player p = new HumanPlayer(playerNumber, "Bob");
		int testIndex = 6;
		ArrayList<Integer> colors = new ArrayList<>();
		ArrayList<Ring> rings = new ArrayList<>();
		rings.add(new Ring(3, playerNumber, 2, true));
		
		colors.add(2);
		
		ViewTUI.staticPrintline(board.index(testIndex)[0] + " " + board.index(testIndex)[1]);
		
		//Make sure player has no moves if they have no rings
		assertTrue(board.availableMoves(p).size() == 0);
		
		int color = 0;
		int size = 0;
		
		// Starting base an adding it to the board to
		Ring r = new Ring(size, playerNumber, color, false);
		board.getNode(testIndex).setRing(0, 0, r);
		
		// Giving player normal rings 
		p.setRings(rings);
		p.setColors(colors);
		ViewTUI.staticPrintline(board.toString());
		ViewTUI.staticPrintline("" + p.getPlayerRings());
		ViewTUI.staticPrintline("" + board.availableMoves(p));
		assertTrue(board.availableMoves(p).size() == 4);
	}

}
