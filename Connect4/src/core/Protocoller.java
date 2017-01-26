package core;

import java.awt.Point;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.Socket;
import core.protocol.ChatCapabilityClient;
import core.protocol.Connect4Client;

public class Protocoller implements Connect4Client, ChatCapabilityClient {

	private Client client;
	private final String address;
	private final int port;
	private final Socket sock;
	
	//@ requires client != null;
	public Protocoller(Client client, String addressAndPort) throws MalFormedServerAddressException, ServerNotFoundException {
		this.client = client;
		try {
			String[] parts = addressAndPort.split(":");
			this.address = parts[0];
			this.port = Integer.parseInt(parts[1]);
		} catch (Exception e) {
			throw new MalFormedServerAddressException(addressAndPort);
		}
		try {
			sock = new Socket(address, port);
		} catch (IOException e) {
			throw new ServerNotFoundException(address, port);
		}
		new InputHandler().start();
	}

	@Override
	public void cmdMove(int x, int y) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void cmdChat(int recipientID, String msg) {
		// TODO Auto-generated method stub
		
	}

	private class InputHandler extends Thread {
		
		private BufferedReader br;
		
		public InputHandler() {
			try {
				br = new BufferedReader(new InputStreamReader(sock.getInputStream()));
			} catch (IOException e) {
				System.err.println("Error while getting inputStream from the server");
				System.err.println(e.getMessage());
				System.err.println("Communication from the ");
			}
		}
		
		@Override
		public void run() {
			try {
				String input;
				while ((input = br.readLine()) != null) {
					client.getView().internalMessage("input from server received: " + input);
					parse(input);
				}
			} catch (IOException e) {
				new InputHandler().start();
			}
		}
	}

	public void parse(String input) throws UnknownServerCommandFormatException {
		if (input.startsWith(CMD_WELCOME)) {
			input = input.substring(CMD_WELCOME.length()).trim();
			String[] args = input.split("[\\s,]+");
			try {
				client.welcomed(Integer.parseInt(args[0]),
						Integer.parseInt(args[1]),
						Integer.parseInt(args[2]));
			} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
				throw new UnknownServerCommandFormatException(CMD_WELCOME, input);
			}
		}
	}
	
	//Core functionality
	private static final String CMD_WELCOME = "WELCOME";
	private static final String CMD_GAME = "GAME";
	private static final String CMD_MOVE_SUCCESS = "MOVE_SUCCESS";
	private static final String CMD_GAME_END = "GAME_END";
	private static final String CMD_LEFT = "LEFT";
	
	//Chat capability
	private static final String CMD_CHAT_MSG = "CHAT_MSG";
}
