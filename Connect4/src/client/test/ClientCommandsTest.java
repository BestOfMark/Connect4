package client.test;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.ServerSocket;
import java.net.Socket;

/**
 * This Class checks whether the Client is capable of correctly formats the commands send to the 
 * server 
 * Requires the client to be controller manually, output should be read on both the server and 
 * client console.
 */

public class ClientCommandsTest {
	
	
	@SuppressWarnings("resource")
	public static void main(String[] args) {
		
		try {
			// open server socket and set up BufferedReader and BufferedWriter and 
			//await for the client to connect
			ServerSocket ss = new ServerSocket(666);
			Socket sock = new Socket();
			sock = ss.accept();
			BufferedReader br = new BufferedReader(new InputStreamReader(sock.getInputStream()));
			BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
			
			// Client connects with Hello command
			System.out.println(br.readLine());
			//Expected response
			System.out.println("HELLO" + " " + "username" + " " + "boolean" + " " + "magicnumber");
			
			//Server responds with Wrongly formatted Welcome command
			bw.write("WELCOME " + "0600000");
			bw.newLine();
			bw.flush();
			Thread.sleep(5000);
			
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
			
			//Server waits for the Client to send a chat message
			System.out.println(br.readLine());
			//Expected response
			System.out.println("CHAT" + " " + "SOME CHAT MESSAGE");
			
			//Server sends Game_end client is the winner, client stops the game, 
			//but stays connected to the server.
			bw.write("GAME_END " + "0");
			bw.newLine();
			bw.flush();
			Thread.sleep(5000);
			
			//Server Tries to start a new game, but uses wrong format.
			bw.write("Game " + "SetToFail " + "10" + "44404");
			bw.newLine();
			bw.flush();
			Thread.sleep(5000);
			
			//Server Starts a new game, sets the client to wait for an opponent to make a move
			bw.write("GAME " + "Tegenstander2 " + "11 " + "4 " + "4 " + "4 " + "11 " + "4");
			bw.newLine();
			bw.flush();
			Thread.sleep(5000);
			
			//Server Sends a chat message to the client
			bw.write("CHAT_MSG" + " " + "11" + " " + "Test Chat");
			bw.newLine();
			bw.flush();
			Thread.sleep(5000);
			
			//Server sends a wrongly formatted Move_succes, client outputs server input, 
			//but doesn't recognize it as a Server Command.
			bw.write("MOVE_SUCCES " + "0 " + "0 " + "11 " + "0");
			bw.newLine();
			bw.flush();
			
			//Server sends a Move_success to the client, expecting him to make the next move.
			bw.write("MOVE_SUCCESS " + "0 " + "0 " + "11 " + "0");
			bw.newLine();
			bw.flush();
			Thread.sleep(5000);
			
			//Client responds with a move.
			System.out.println(br.readLine());
			//Expected response
			System.out.println("MOVE" + " " + "int" + " " + "int");
			
			//Server responds by sending Illegal, the Client expected to disconnect if it is an 
			//AI otherwise it will try to make a move again.
			bw.write("ILLEGAL " + "CLIENT_MOVE Illegal");
			bw.newLine();
			bw.flush();
			Thread.sleep(5000);
			
			//Server tries to send opponent Left, but uses wrong format
			bw.write("LEFT ");
			bw.newLine();
			bw.flush();
			Thread.sleep(5000);
			
			//Server sends Opponent left, the client will go to the connection state.
			bw.write("LEFT " + "11 " + "opponent left");
			bw.newLine();
			bw.flush();
			Thread.sleep(5000);
			
			//Server starts a new game
			bw.write("GAME" + "Tegenstander2 " + "12 " + "4 " + "4 " + "4 " + "12 " + "4");
			bw.newLine();
			bw.flush();
			Thread.sleep(5000);
			
			//Test ends, the client should print connection lost
			
			
		} catch (IOException | InterruptedException e) {
			e.printStackTrace();
		}
		
		
		
	}

}
