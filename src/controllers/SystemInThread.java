package controllers;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;

/**
 * SystemInThread class.
 * Programming project, Software Systems
 * 
 * @author Arnav Mundkur and Paulius Gagelas
 * @version 2018.01.31
 */
public class  SystemInThread extends Thread {
	private PrintWriter printWriter;

	public SystemInThread(PrintWriter p) {
		printWriter = p;
	}

	public void run() {
		BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
		String input;
		while (true) {
			try {
				input = br.readLine();
				printWriter.println(input);
				printWriter.flush();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
}
