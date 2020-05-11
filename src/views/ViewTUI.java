package views;
 
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Observable;
import java.util.Observer;
import java.util.Scanner;

import controllers.LocalGame;
import controllers.NetworkGame;

/**
 * ViewTUI class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class ViewTUI implements Observer {
	private Scanner in;
	private static Scanner line;

	public ViewTUI(NetworkGame game) {
	}
	
	public ViewTUI(LocalGame game) {
	}

	public synchronized static void staticPrintline(String message) {
		System.out.println(message);
	}

	public synchronized static void staticPrint(String message) {
		System.out.print(message);
	}

	public synchronized void println(String message) {
		System.out.println(message);
	}
	
	public synchronized void print(String message) {
		System.out.print(message);
	}

	public static void startingInfo(int playerCount) {
		System.out.println("Making a game with " + playerCount + " players");
	}

	/**
	 * Method for showing what choices the user has.
	 */
	public void showHelp() {
		System.out.println("All the choices: ");
	}

	/**
	 * Writes a prompt to standard out and tries to read an int value from
	 * standard in. This is repeated until an int value is entered.
	 * 
	 * @param prompt
	 *            the question to prompt the user
	 * @return the first int value which is entered by the user
	 */
	public static int readInt(String prompt) {
		int value = 0;
		boolean intRead = false;
		line = new Scanner(System.in);
		do {
			System.out.print(prompt);
			try (Scanner scannerLine = new Scanner(line.nextLine())) {
				if (scannerLine.hasNextInt()) {
					intRead = true;
					value = scannerLine.nextInt();
				}
			}
		} while (!intRead);
		return value;
	}

	public static String readString(String prompt) {
		String value = "";
		boolean stringRead = false;
		line = new Scanner(System.in);
		do {
			System.out.print(prompt);
			try (Scanner scannerLine = new Scanner(line.nextLine())) {
				if (scannerLine.hasNextLine()) {
					stringRead = true;
					value = scannerLine.nextLine();
				}
			}
		} while (!stringRead);
		return value;
	}

	/**
	 * Prints a question which can be answered by yes (true) or no (false).
	 * 
	 * @parom prompt the question to print
	 * @param yes
	 *            the String corresponding to a yes answer
	 * @param no
	 *            the String corresponding to a no answer
	 * @return true is the yes answer is typed, false if the no answer is typed
	 */
	public boolean readBoolean(String prompt, String yes, String no) {
		String answer;
		in = new Scanner(System.in);
		do {
			System.out.print(prompt);
			answer = in.hasNextLine() ? in.nextLine() : null;
		} while (answer == null || (!answer.equals(yes) && !answer.equals(no)));
		return answer.equals(yes);
	}

	/**
	 * Prints a question which can be answered by yes (true) or no (false).
	 * 
	 * @parom prompt the question to print
	 * @param yes
	 *            the String corresponding to a yes answer
	 * @param no
	 *            the String corresponding to a no answer
	 * @return true is the yes answer is typed, false if the no answer is typed
	 */
	public static boolean[] readBooleans(String prompt) {
		boolean[] result = new boolean[4];
		String input;
		line = new Scanner(System.in);
		boolean valid = false;
		
		do {
			System.out.print(prompt);
			input = line.hasNextLine() ? line.nextLine() : null;
			int valuesChecked = 0;
			if (input.startsWith("SUPPORTS")) {
				String value = input.substring(9);
				String[] values = value.split(" ");

				for (int i = 0; i < values.length; i++) {
					if (values[i].equals("false") || values[i].equals("true")) {
						result[i] = Boolean.parseBoolean(values[i]);
						valuesChecked++;
					}
				}
				
				if (valuesChecked == result.length) {
					valid = true;
				} else {
					System.out.println("Wrong format: Only true or false values are accepted");
				}
			}
		} while (!valid);
		return result;
	}
	
	public static InetAddress getIp(String host) {
		InetAddress addr = null;
		try {
			addr = InetAddress.getByName(host);
		} catch (UnknownHostException e) {
			return null;
		}
		return addr;
	}

	public static int getPort(String portstr) {
		int port = 0;
		try {
			port = Integer.parseInt(portstr);
		} catch (NumberFormatException e) {
			return 0;
		}
		return port;
	}

	@Override
	public void update(Observable o, Object arg) {
	}
}
