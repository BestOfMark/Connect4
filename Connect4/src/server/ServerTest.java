package server;

import java.io.*;
import java.net.Socket;
import java.net.UnknownHostException;

public class ServerTest {
	
	private static Socket sock;
	
	public static void main(String[] args) {
		try {
			sock = new Socket("localhost", 666);
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
			System.out.println("Exiting server listener");
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
