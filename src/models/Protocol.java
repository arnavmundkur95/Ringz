package models;

/**
 * Protocol class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class Protocol {
	// Setup commands
	public static final String SUPPORTS = "SUPPORTS";
	public static final String CONNECT = "CONNECT";
	public static final String START_GAME = "START_GAME";

	// Gameplay commands
	public static final String MOVE = "MOVE";
	public static final String MOVE_ACCEPTABLE = "MOVE_ACCEPTABLE";
	public static final String PLAYER_TURN = "PLAYER_TURN";

	// Post game commands
	public static final String SCORES = "SCORES";
	public static final String PLAY_AGAIN = "PLAY_AGAIN";

	// Extra commands
	public static final String REGISTER = "REGISTER";
	public static final String REGISTERED = "REGISTERED";
	public static final String NAME_INVALID = "NAME_INVALID";
	public static final String PASSWORD_INVALID = "PASSWORD_INVALID";
	public static final String LOGIN = "LOGIN";
	public static final String LOGGED_IN = "LOGGED_IN";
	public static final String LOGIN_INVALID = "LOGIN_INVALID";
	public static final String CHAT = "CHAT";
	public static final String DISCONNECT = "DISCONNECT";
	public static final String LEADERBOARD = "LEADERBOARD";
	public static final String MY_LEADERBOARD = "MY_LEADERBOARD";
	public static final String CHALLENGE = "CHALLENGE";
	public static final String CHALLENGEES = "CHALLENGEES";
	public static final String CHALLENGE_ACCEPT = "CHALLENGE_ACCEPT";
	public static final String INVALID_CHALLENGE = "INVALID_CHALLENGE";
}
