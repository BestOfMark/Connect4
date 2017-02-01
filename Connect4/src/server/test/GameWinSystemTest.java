package server.test;

import java.io.*;
import java.net.Socket;
import java.util.HashMap;

public class GameWinSystemTest {
	
	private static HashMap<Integer, BufferedReader> brMap;
	private static HashMap<Integer, BufferedWriter> bwMap;
	
	public static void main(String[] args) {
		try {
			//Initialize maps
			brMap = new HashMap<>();
			bwMap = new HashMap<>();
			
			//Set up fake client 1 (c1)
			Socket sock1 = new Socket("localhost", 666);
			BufferedReader br1 = new BufferedReader(new InputStreamReader(sock1.getInputStream()));
			BufferedWriter bw1 = new BufferedWriter(new OutputStreamWriter(
					sock1.getOutputStream()));
			brMap.put(1, br1);
			bwMap.put(1, bw1);
			
			//Set up fake client 2 (c1)
			Socket sock2 = new Socket("localhost", 666);
			BufferedReader br2 = new BufferedReader(new InputStreamReader(sock2.getInputStream()));
			BufferedWriter bw2 = new BufferedWriter(new OutputStreamWriter(
					sock2.getOutputStream()));
			brMap.put(2, br2);
			bwMap.put(2, bw2);
			
			//Hello from c1, wait for WELCOME response server
			sendCommand(1, "HELLO P1 false 0");
			waitForResponse(1);
			Thread.sleep(500);
			
			//Hello from c2, wait for WELCOME response server
			sendCommand(2, "HELLO P2 false 0");
			waitForResponse(2);
			Thread.sleep(500);
			
			//Request from c1, ready for a game
			sendCommand(1, "REQUEST");
			Thread.sleep(500);
			
			//Request from c2, ready for a game, game should start now that 2 players are ready
			sendCommand(2, "REQUEST");
			waitForResponse(1);
			Thread.sleep(500);
			
			//Move from c1, Expects MOVE_SUCCESS from server
			sendCommand(2, "MOVE 0 0");
			waitForResponse(1);
			waitForResponse(2);
			Thread.sleep(500);
			
			//Chat c1, c2 receives chat
			sendCommand(1, "CHAT " + "test message");
			waitForResponse(2);
			Thread.sleep(500);
			
			//Move from c1, ILLEGAL response expected from server
			sendCommand(2, "MOVE " + "0 " + "0");
			waitForResponse(1);
			waitForResponse(2);
			Thread.sleep(100);
			
			//Move from c2, expects MOVE_SUCCESS from server
			sendCommand(1, "MOVE 2 0");
			waitForResponse(1);
			waitForResponse(2);
			Thread.sleep(500);
			
//			//Move from c2, expects MOVE_SUCCESS from server
//			sendCommand(2, "MOVE 5 0");
//			waitForResponse(1);
//			waitForResponse(2);
//			Thread.sleep(500);
			
			//c2 closes socket
			sock2.close();
			
			Thread.sleep(20000);
			
			//Terminate the server for emma
			sendCommand(1, "TERMINATE");
			
			sock1.close();
		} catch (IOException | InterruptedException e) {
			e.printStackTrace();
		}
	}
	
	private static void sendCommand(int client, String cmd) throws IOException {
		System.out.println("OUT (" + client + "): " + cmd);
		BufferedWriter bw = bwMap.get(client);
		bw.write(cmd);
		bw.newLine();
		bw.flush();
	}
	
	private static void waitForResponse(int client) throws IOException {
		System.out.println("IN  (" + client + "): " + brMap.get(client).readLine());
	}
}
