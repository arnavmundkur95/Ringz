
package models;

import java.util.ArrayList;

import views.ViewTUI;
import controllers.NetworkGame;
import controllers.Server;
import controllers.ServerThread;

/**
 * Lobby class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class Lobby {
	public final int capacity;

	// private int currentPlayerAmount = 0;

	/**
	 * The set of all names of clients in the chat room. Maintained so that we can
	 * check that new clients are not registering name already in use.
	 */
	private ArrayList<String> names;

	private ArrayList<ServerThread> handlers;
	private ArrayList<GameThread> games;
	/**
	 * The set of all the print writers for all the clients. This set is kept so we
	 * can easily broadcast messages.
	 */

	public Lobby(int capacity) {
		this.capacity = capacity;
		names = new ArrayList<>();
		handlers = new ArrayList<>();
		games = new ArrayList<>();
	}

	public boolean hasName(String name) {
		for (int i = 0; i < names.size(); i++) {
			if (name.equals(names.get(i))) {
				return true;
			}
		}
		return false;
	}

	public void addPlayer(String name, ServerThread s) {
		names.add(name);
		handlers.add(s);
		s.sendMessage("Hi " + name + ", logged in to " + capacity + " player games lobby");
		s.sendMessage("Waiting for more players to connect, then the game will start!");
		if (lobbyFull()) {
			startGame();
		}
	}

	public boolean lobbyFull() {
		return names.size() == capacity;
	}

	public void startGame() {
		ViewTUI.staticPrintline("Started a game!");
		
		// Arraylists to pass into the game
		ArrayList<String> namesLobby = new ArrayList<>();
		ArrayList<ServerThread> clientsLobby = new ArrayList<>();
		
		for (int i = 0; i < capacity; i++) {
			namesLobby.add(names.get(i));
			clientsLobby.add(handlers.get(i));
		}
		
		String namesToSend = "";
		
		for (int i = 0; i < namesLobby.size(); i++) {
			namesToSend += namesLobby.get(i) + " ";
		}
		
		for (int i = 0; i < clientsLobby.size(); i++) {
			Server.sendToClient(clientsLobby.get(i), Protocol.START_GAME + " " + (i + 1) + 
					" " + namesToSend);
		}

		for (int i = 0; i < capacity; i++) {
			if (names.contains(namesLobby.get(i))) {
				names.remove(namesLobby.get(i));
			}
			
			if (handlers.contains(clientsLobby.get(i))) {
				handlers.remove(clientsLobby.get(i));
			}
		}		
		GameThread gameThread = new GameThread(new NetworkGame(capacity, namesLobby, clientsLobby));
		gameThread.start();
		gameThread.setName("GAME");
		games.add(gameThread);
	}
}
