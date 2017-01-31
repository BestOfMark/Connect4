package client.test;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.ServerSocket;
import java.net.Socket;

/**
 * This Class checks whether the Client is capable of correctly formats the commands send to the server
 */

public class ClientCommandsTest {
	
	
	public static void main(String[] args) {
		
		try {
			// open server socket and set up BufferedReader and BufferedWriter and await for the client to connect
			ServerSocket ss = new ServerSocket(666);
			Socket sock = new Socket();
			sock = ss.accept();
			BufferedReader br = new BufferedReader(new InputStreamReader(sock.getInputStream()));
			BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
			
			// Client connects with Hello command
			System.out.println(br.readLine());
			//Expected response
			System.out.println("HELLO" + " " + "username" + " " + "boolean" + " " + "magicnumber");
			
			//Server responds with Welcome command
			bw.write("WELCOME " + "0 " + "60000 " + "0");
			bw.newLine();
			bw.flush();
			Thread.sleep(10000);
			
			//Client responds with a request for a game
			System.out.println(br.readLine());
			//Expected response
			System.out.println("REQUEST");
			
			//Server responds with starting a Game
			bw.write("GAME " + "Tegenstander " + "10 " + "4 " + "4 " + "4 " + "0 " + "4");
			bw.newLine();
			bw.flush();
			Thread.sleep(10000);
			
			//Client responds with a move
			System.out.println(br.readLine());
			//Expected response
			System.out.println("MOVE" + " " + "int" + " " + "int");
			
			//Server responds with a move_success, client doesn't respond but enters wait state
			bw.write("MOVE_SUCCESS " + "0 " + "0 " + "0 " + "10");
			bw.newLine();
			bw.flush();
			Thread.sleep(10000);
			
			//Serve waits for the Client to send a chat message
			System.out.println(br.readLine());
			//Expected response
			System.out.println("CHAT" + " " + "SOME CHAT MESSAGE");
			
			
		} catch (IOException | InterruptedException e) {
			e.printStackTrace();
		}
		
		
		
	}

}
