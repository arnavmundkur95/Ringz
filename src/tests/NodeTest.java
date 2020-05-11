package tests;

import static org.junit.jupiter.api.Assertions.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import models.Node;
import models.Ring;
import views.ViewTUI;
/**
 * NodeTest class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
class NodeTest {

	private Node node;

	@BeforeEach
	void setUp() throws Exception {
		node = new Node(0, 0);
	}

	@Test
	public void isEmptyNodeTest() {
		assertTrue(node.isEmptyNode());
		Ring ring = new Ring(1, 0, 1, false);
		node.setRing(1, 1, ring);
		assertFalse(node.isEmptyNode());
	}

	@Test
	public void isEmptyRingTest() {
		assertTrue(node.isEmptyRing(2));
		Ring ring = new Ring(1, 0, 1, false);
		node.setRing(1, 1, ring);
		assertFalse(node.isEmptyRing(1));
	}

	@Test
	public void isFullTest() {
		Ring[] temp = node.getRingsOnNode();
		assertFalse(temp.length == 0);
		Ring r = new Ring(0, 1, 2, true);
		node.setRing(2, 0, r);
		assertTrue(node.isFull());
	}

	@Test
	public void getRingsOnNodeTest() {
		int[] test = {8, 8, 8, 9, 8, 8, 8 };
		for (int i = 0; i < test.length; i++) {
			assertTrue(test[i] == node.getVisualRings()[i]);
		}
		
		Ring r = new Ring(1, 1, 1, true);
		node.setRing(1, 1, r);
		
		int[] test2 = {8, 8, 8, 1, 8, 8, 8 };
		for (int i = 0; i < test2.length; i++) {
			assertTrue(test2[i] == node.getVisualRings()[i]);
		}
		
	}

	@Test
	public void resetNodeTest() {
		int[] test = {8, 8, 8, 9, 8, 8, 8 };
		Ring r = new Ring(3, 1, 1, false);
		node.setRing(1, 3, r);
		node.resetNode();
		for (int i = 0; i < node.getRingsOnNode().length; i++) {
			assertTrue(test[i] == node.getVisualRings()[i]);
		}
		assertTrue(node.getWonNode() == -1);

	}

	@Test
	public void setRingTest() {
		int check1 = node.getVisualRings()[3];
		int check2 = node.getVisualRings()[2];
		int check22 = node.getVisualRings()[4];
		int check3 = node.getVisualRings()[1];
		int check32 = node.getVisualRings()[5];
		int check4 = node.getVisualRings()[0];
		int check42 = node.getVisualRings()[6];

		assertTrue(node.isEmptyNode());

		// check base

		node.resetNode();
		Ring r = new Ring(0, 1, 2, true);
		node.setRing(2, 0, r);
		for (int i : node.getVisualRings()) {
			ViewTUI.staticPrintline("" + i);
		}
		// checking each position
		r = new Ring(1, 1, 1, true);
		node.setRing(1, 1, r);
		assertTrue(check1 != node.getVisualRings()[3]);
		
		r = new Ring(2, 1, 1, true);
		node.setRing(1, 2, r);
		assertTrue(check2 != node.getVisualRings()[2] && check22 != node.getVisualRings()[4]);
		
		r = new Ring(3, 1, 1, true);
		node.setRing(1, 3, r);
		assertTrue(check3 != node.getVisualRings()[1] && check32 != node.getVisualRings()[5]);
		
		
		r = new Ring(4, 1, 1, true);
		node.setRing(1, 4, r);
		assertTrue(check4 != node.getVisualRings()[0] && check42 != node.getVisualRings()[6]);
	}

}
