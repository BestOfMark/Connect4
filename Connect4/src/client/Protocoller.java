package client;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;

import client.protocol.ChatCapabilityClient;
import client.protocol.Connect4Client;

public class Protocoller implements Connect4Client, ChatCapabilityClient {

	private Client client;
	private final String address;
	private final int port;
	private final Socket sock;
	private BufferedWriter bw;
	private InputHandler ih;
	
	public static final String COMMAND_DELIMITER = " ";
	
	//@ requires client != null;
	public Protocoller(Client client, String addressAndPort) throws MalFormedServerAddressException, ServerNotFoundException, ServerCommunicationException {
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
		try {
			(ih = new InputHandler()).start();
		} catch (IOException e) {
//			System.err.println("Error while getting inputStream from the socket");
			System.err.println(e.getMessage());
			throw new ServerCommunicationException("Communication from the server is not possible");
		}
		try {
			bw = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
		} catch (IOException e) {
//			System.err.println("Error while getting outputStream from the socket");
			System.err.println(e.getMessage());
			throw new ServerCommunicationException("Communication to the server is not possible");
		}
	}
	
	@Override
	public void cmdHello(String username, boolean isAi, int clientCapabilities) throws IOException {
		bw.write(String.join(COMMAND_DELIMITER, CLIENT_HELLO, username, String.valueOf(isAi), String.valueOf(clientCapabilities)));
	}

	@Override
	public void cmdMove(int x, int y) throws IOException {
		bw.write(String.join(COMMAND_DELIMITER, CLIENT_MOVE, String.valueOf(x), String.valueOf(y)));
		
	}

	@Override
	public void cmdChat(int recipientID, String msg) throws IOException {
		bw.write(String.join(COMMAND_DELIMITER, CLIENT_CHAT, String.valueOf(recipientID), msg));
	}
	
	public static final String CLIENT_HELLO = "HELLO";
	public static final String CLIENT_MOVE = "MOVE";
	public static final String CLIENT_CHAT = "CHAT";
	
	public void close() {
		ih.isCloseRequested = true;
	}

	private class InputHandler extends Thread {
		
		private BufferedReader br;
		private boolean isCloseRequested = false;
		
		public InputHandler() throws IOException {
			br = new BufferedReader(new InputStreamReader(sock.getInputStream()));
			
		}
		
		@Override
		public void run() {
			try {
				String input;
				while (!isCloseRequested && (input = br.readLine()) != null) {
					client.getView().internalMessage("input from server received: " + input);
					try {
						parse(input);
					} catch (CommandFormatException e) {
						client.getView().internalMessage(e.getMessage());
					}
				}
			} catch (IOException e) {
				client.getView().internalMessage("Error in Protocol.InputHandler. Trying to restore...");
				try {
					(ih = new InputHandler()).start();
				} catch (IOException e1) {
					e1.printStackTrace();
				}
			}
		}
	}

	private static final String EXCEPTION_SOURCE_NAME = "Server";
	public void parse(String input) throws CommandFormatException {
		if (input.startsWith(SERVER_WELCOME)) {
			input = input.substring(SERVER_WELCOME.length()).trim();
			String[] args = input.split("[\\s,]+");
			try {
				client.welcomed(
						Integer.parseInt(args[0]),
						Integer.parseInt(args[1]),
						Integer.parseInt(args[2]));
			} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
				throw new CommandFormatException(SERVER_WELCOME, input, EXCEPTION_SOURCE_NAME);
			}
		} else if (input.startsWith(SERVER_GAME)) {
			input = input.substring(SERVER_GAME.length()).trim();
			String[] args = input.split("[\\s,]+");
			try {
				client.newGame(
						args[0],
						Integer.parseInt(args[1]),
						Integer.parseInt(args[2]),
						Integer.parseInt(args[3]),
						Integer.parseInt(args[4]),
						Integer.parseInt(args[5]),
						Integer.parseInt(args[6]));
			} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
				throw new CommandFormatException(SERVER_GAME, input, EXCEPTION_SOURCE_NAME);
			}
		} else if (input.startsWith(SERVER_MOVE_SUCCESS)) {
			input = input.substring(SERVER_MOVE_SUCCESS.length()).trim();
			String[] args = input.split("[\\s,]+");
			try {
				client.receivedMove(
						Integer.parseInt(args[0]),
						Integer.parseInt(args[0]),
						Integer.parseInt(args[0]),
						Integer.parseInt(args[0]));
			} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
				throw new CommandFormatException(SERVER_MOVE_SUCCESS, input, EXCEPTION_SOURCE_NAME);
			}
		} else if (input.startsWith(SERVER_GAME_END)) {
			input = input.substring(SERVER_GAME_END.length()).trim();
			try {
				client.gameOver(
						Integer.parseInt(input));
			} catch (NumberFormatException e) {
				throw new CommandFormatException(SERVER_GAME_END, input, EXCEPTION_SOURCE_NAME);
			}
		} else if (input.startsWith(SERVER_LEFT)) {
			input = input.substring(SERVER_MOVE_SUCCESS.length()).trim();
			String[] args = input.split("[\\s,]+");
			try {
				client.opponentLeft(
						Integer.parseInt(args[0]),
						args[1]);
			} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
				throw new CommandFormatException(SERVER_LEFT, input, EXCEPTION_SOURCE_NAME);
			}
		} else if (input.startsWith(SERVER_ILLEGAL)) {
			input = input.substring(SERVER_ILLEGAL.length()).trim();
			client.illegalCommand(input);
		} else if (input.startsWith(SERVER_CHAT_MSG)) {
			input = input.substring(SERVER_CHAT_MSG.length()).trim();
			String[] args = input.split("[\\s,]+");
			try {
				client.chatReceived(
						Integer.parseInt(args[0]),
						args[1]);
			} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
				throw new CommandFormatException(SERVER_CHAT_MSG, input, EXCEPTION_SOURCE_NAME);
			}
		}
	}
	
	//Core functionality 
	public static final String SERVER_WELCOME = "WELCOME";
	public static final String SERVER_GAME = "GAME";
	public static final String SERVER_MOVE_SUCCESS = "MOVE_SUCCESS";
	public static final String SERVER_GAME_END = "GAME_END";
	public static final String SERVER_LEFT = "LEFT";
	public static final String SERVER_ILLEGAL = "ILLEGAL";
	
	//Chat capability
	public static final String SERVER_CHAT_MSG = "CHAT_MSG";
}
