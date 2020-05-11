package controllers;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;

import models.ChangeListener;
import models.Lobby;
import models.Protocol;
import views.ViewTUI;

/**
 * ServerThread class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class ServerThread extends Thread {

	public static final String EMPTY = "EMPTY";
	private boolean connected;
	private boolean supported; // Used to check if we received a SUPPORTS from server
	private boolean myTurn;
	private int playAgain;
	private String attemptedMove;
	private String move;
	
	private Socket socket;
	private PrintWriter writer;
	private Server server;
	private InputStreamReader is;
	private BufferedReader br;
	private ChangeListener listener;

	public ServerThread(Socket s, Server server) {
		socket = s;
		try {
			writer = new PrintWriter(socket.getOutputStream(), true);
			is = new InputStreamReader(socket.getInputStream());
			br = new BufferedReader(is);

		} catch (IOException e) {
			e.printStackTrace();
		}
		this.server = server;
		connected = false;
		supported = false;
		move = EMPTY;
		attemptedMove = null;
		playAgain = 0;
	}

	public void run() {
		String m;
		String[] splitMessage;
		String command; // The command the Client wrote
		while (true) {
			try {
				while ((m = br.readLine()) != null) {
					splitMessage = m.split(" ");
					command = splitMessage[0];
					
					if (command.equals(Protocol.LOGIN)
							|| command.equals(Protocol.CHALLENGE)
							|| command.equals(Protocol.REGISTER) 
							|| command.equals(Protocol.CHALLENGEES)
							|| command.equals(Protocol.LEADERBOARD) 
							|| command.equals(Protocol.MY_LEADERBOARD)) {
						sendMessage("Currently " + command + " is not supported");
					}
					
					if (connected) {
						if (command.equals(Protocol.MOVE)) {
							if (myTurn) {
								ViewTUI.staticPrintline("Got a move!");
								ViewTUI.staticPrintline("got this move: " + m);
								
								attemptedMove = m;
								listener.onChange();
							} else { // To get other player's moves
								sendMessage(m);
								myTurn = false;
							}
							myTurn = false;
						} else if (command.equals(Protocol.PLAY_AGAIN)) {
							if (splitMessage[1].equals("true")) {
								playAgain = 1;
							} else if (splitMessage[1].equals("false")) {
								playAgain = 2;
							}
						}
					} else if (supported && command.equals(Protocol.CONNECT)) {
						connectUser(m);
						connected = true;
					} else if (command.equals(Protocol.SUPPORTS)) {
						boolean[] serverSupports = {false, false, false, false};
						String supports = "SUPPORTS ";
						
						for (int i = 0; i < serverSupports.length; i++) {
							supports += serverSupports[i] + " ";
						}
						sendMessage(supports);
						supported = true;
					} 
				}

			} catch (IOException e) {
				e.printStackTrace();
				System.exit(-1);
			}
		}
	}
	
	public int getPlayAgain() {
		return playAgain;
	}
	
	public void resetPlayAgain() {
		playAgain = 0;
	}
	
	public void setChangeListener(ChangeListener changeListener) {
		listener = changeListener;
	}

	public void sendMessage(String s) {
		writer.println(s);
		writer.flush();
	}

	public boolean connectUser(String input) {
		String[] values = input.split(" ");
		String name = values[1];

		String lobbyNumber = values[2];
		int lobbyInt = 0;

		// Parse lobby number
		try {
			lobbyInt = Integer.parseInt(lobbyNumber);
		} catch (NumberFormatException e) {
			e.printStackTrace();
			return false;
		}

		// Check lobby number
		if (lobbyInt > 4 || lobbyInt < 0 || lobbyInt == 1) {
			sendMessage("No such lobby");
			return false;
		}

		// Get the lobby we want
		Lobby lobby = server.getLobby(lobbyInt);

		// Check name
		boolean hasName = lobby.hasName(name);
		if (hasName) {
			sendMessage("Choose a different username");
		}
		lobby.addPlayer(name, this);
		return true;
	}

	public void setIsTurn(boolean b) {
		myTurn = b;
	}

	public void shutdown() {
		try {
			socket.close();
			server.removeClient(this);

		} catch (IOException e) {
			ViewTUI.staticPrintline("Error shutting down");
		}
	}

	public String getMove() {
		return move;
	}

	public synchronized void resetMove() {
		move = EMPTY;
	}

	public  void resetAttemptedMove() {
		attemptedMove = null;

	}
	
	public synchronized String getAttemptedMove() {
		return attemptedMove;
	}

	public synchronized void setMove() {
		move = attemptedMove;
	}
}
