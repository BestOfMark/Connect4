package client.test;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.UnknownHostException;


/**
 * This Class opens a dummy server controlled via the command window.
 * A client can connect to the dummy server, allowing for flexible debugging by the user.
 */

public class ClientTest {
	
	private static ServerSocket ss;
	private static Socket sock;
	
	public static void main(String[] args) {
		try {
			ss = new ServerSocket(666);
			sock = ss.accept();
			new InputListener().start();
			new ConsoleListener().start();
		} catch (UnknownHostException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	private static class InputListener extends Thread {
	
		@Override
		public void run() {
			BufferedReader br = null;
			try {
				br = new BufferedReader(new InputStreamReader(sock.getInputStream()));
			} catch (IOException e1) {
				e1.printStackTrace();
			}
			String line;
			try {
				while ((line = br.readLine()) != null) {
					System.out.println(line);
				}
			} catch (IOException e) {
				e.printStackTrace();
			}
			System.out.println("Exiting client listener");
		}
	}

	private static class ConsoleListener extends Thread {
	
		@Override
		public void run() {
			BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
			BufferedWriter bw = null;
			try {
				bw = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
			} catch (IOException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
			String line;
			try {
				while ((line = br.readLine()) != null) {
					System.out.println("ECHO: " + line);
					bw.write(line);
					bw.newLine();
					bw.flush();
				}
			} catch (IOException e) {
				e.printStackTrace();
			}
			System.out.println("Exiting console listener");
		}
	}

}
