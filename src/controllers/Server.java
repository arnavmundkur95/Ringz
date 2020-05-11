
package controllers;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;

import models.Lobby;
import views.ViewTUI;

/**
 * Server class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class Server {
	private static final String USAGE = "Usage: <port>";
	private ArrayList<ServerThread> clients = new ArrayList<>();
	private ServerSocket serverSocket;
	private static int portNumber = 1234;
	private static final int LOBBY_AMOUNT = 4;
	private Lobby[] lobbies = new Lobby[LOBBY_AMOUNT];

	public Server(ServerSocket serv) {
		for (int i = 0; i < LOBBY_AMOUNT; i++) {
			if (i == 0) {
				lobbies[i] = new Lobby(0);
				continue;
			}
			lobbies[i] = new Lobby(i + 1);
		}
		this.serverSocket = serv;
	}
	
	public Lobby getLobby(int capacity) {
		for (int i = 0; i < lobbies.length; i++) {
			// Find lobby of that size
			if (capacity == lobbies[i].capacity) {
				return lobbies[i];
			}
		}
		return null;
	}

	
	public void addPlayer(String name, String gameSize, ServerThread s) {
		for (int i = 0; i < lobbies.length; i++) {
			// Find lobby of that size
			if (Integer.parseInt(gameSize) == lobbies[i].capacity) {
				lobbies[i].addPlayer(name, s);
			}
		}
	}


	/** Method for starting a server. */
	public static void main(String[] args) throws IOException {

		int port = 0;
		
		if (args.length == 1) {
			port = ViewTUI.getPort(args[0]);
		} else if (args.length > 1) {
			ViewTUI.staticPrintline(USAGE);
			System.exit(1);
		} 

		if (port == 0) {
			port = portNumber;
		}
		
		ServerSocket serv = null;
		try {
			serv = new ServerSocket(port);
		} catch (IOException e1) {
			ViewTUI.staticPrintline("Server already open!");
			System.exit(1);
		}
		
		Server server = new Server(serv);
		ViewTUI.staticPrintline("Starting a server on port " + port);
		server.acceptor();
	}

	public void acceptor() throws IOException {
		while (true) {
			Socket sock = serverSocket.accept();
			ViewTUI.staticPrintline("New client connected!");

			ServerThread serverThread = new ServerThread(sock, this);
			clients.add(serverThread);
			serverThread.start();
		}
	}
	
	public void removeClient(ServerThread c) {
		clients.remove(c);
	}
	
	public static void sendToClient(ServerThread s, String message) {
		s.sendMessage(message);
	}
	
	public static void sendToGamers(ArrayList<ServerThread> s, String message) {
		for (int i = 0; i < s.size(); i++) {
			s.get(i).sendMessage(message);
		}
	}
}
