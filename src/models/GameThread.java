package models;

import controllers.NetworkGame;

public class GameThread extends Thread{
	
	NetworkGame game;
	
	public GameThread(NetworkGame g) {
		game = g;
		
	}
	
	public void run() {
		game.startGame();
	}

}
