package core;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import core.protocol.ChatCapabilityClient;
import core.protocol.Connect4Client;

public class Protocoller implements Connect4Client, ChatCapabilityClient {

	private Client client;
	private final String address;
	private final int port;
	private final Socket sock;
	private BufferedWriter bw;
	private InputHandler ih;
	
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
		bw.write(String.join(CMD_DELIMITER, CMD_HELLO, username, String.valueOf(isAi), String.valueOf(clientCapabilities)));
	}

	@Override
	public void cmdMove(int x, int y) throws IOException {
		bw.write(String.join(CMD_DELIMITER, CMD_MOVE, String.valueOf(x), String.valueOf(y)));
		
	}

	@Override
	public void cmdChat(int recipientID, String msg) throws IOException {
		bw.write(String.join(CMD_DELIMITER, CMD_CHAT, String.valueOf(recipientID), msg));
	}
	
	private static final String CMD_DELIMITER = " ";
	private static final String CMD_HELLO = "HELLO";
	private static final String CMD_MOVE = "MOVE";
	private static final String CMD_CHAT = "CHAT";
	
	public void close() {
		ih.close();
	}

	private class InputHandler extends Thread {
		
		private BufferedReader br;
		private boolean isCloseRequested = false;
		
		public InputHandler() throws IOException {
			br = new BufferedReader(new InputStreamReader(sock.getInputStream()));
			
		}
		
		public void close() {
			isCloseRequested = true;
		}
		
		@Override
		public void run() {
			try {
				String input;
				while (!isCloseRequested && (input = br.readLine()) != null) {
					client.getView().internalMessage("input from server received: " + input);
					try {
						parse(input);
					} catch (UnknownServerCommandFormatException e) {
						client.getView().internalMessage("could not parse server command");
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

	public void parse(String input) throws UnknownServerCommandFormatException {
		if (input.startsWith(CMD_WELCOME)) {
			input = input.substring(CMD_WELCOME.length()).trim();
			String[] args = input.split("[\\s,]+");
			try {
				client.welcomed(
						Integer.parseInt(args[0]),
						Integer.parseInt(args[1]),
						Integer.parseInt(args[2]));
			} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
				throw new UnknownServerCommandFormatException(CMD_WELCOME, input);
			}
		} else if (input.startsWith(CMD_GAME)) {
			input = input.substring(CMD_GAME.length()).trim();
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
				throw new UnknownServerCommandFormatException(CMD_GAME, input);
			}
		} else if (input.startsWith(CMD_MOVE_SUCCESS)) {
			input = input.substring(CMD_MOVE_SUCCESS.length()).trim();
			String[] args = input.split("[\\s,]+");
			try {
				client.receivedMove(
						Integer.parseInt(args[0]),
						Integer.parseInt(args[0]),
						Integer.parseInt(args[0]),
						Integer.parseInt(args[0]));
			} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
				throw new UnknownServerCommandFormatException(CMD_MOVE_SUCCESS, input);
			}
		} else if (input.startsWith(CMD_GAME_END)) {
			input = input.substring(CMD_GAME_END.length()).trim();
			try {
				client.gameOver(
						Integer.parseInt(input));
			} catch (NumberFormatException e) {
				throw new UnknownServerCommandFormatException(CMD_GAME_END, input);
			}
		} else if (input.startsWith(CMD_LEFT)) {
			input = input.substring(CMD_MOVE_SUCCESS.length()).trim();
			String[] args = input.split("[\\s,]+");
			try {
				client.opponentLeft(
						Integer.parseInt(args[0]),
						args[1]);
			} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
				throw new UnknownServerCommandFormatException(CMD_LEFT, input);
			}
		} else if (input.startsWith(CMD_ILLEGAL)) {
			input = input.substring(CMD_ILLEGAL.length()).trim();
			client.illegalMove(input);
		} else if (input.startsWith(CMD_CHAT_MSG)) {
			input = input.substring(CMD_CHAT_MSG.length()).trim();
			String[] args = input.split("[\\s,]+");
			try {
				client.chatReceived(
						Integer.parseInt(args[0]),
						args[1]);
			} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
				throw new UnknownServerCommandFormatException(CMD_CHAT_MSG, input);
			}
		}
	}
	
	//Core functionality 
	private static final String CMD_WELCOME = "WELCOME";
	private static final String CMD_GAME = "GAME";
	private static final String CMD_MOVE_SUCCESS = "MOVE_SUCCESS";
	private static final String CMD_GAME_END = "GAME_END";
	private static final String CMD_LEFT = "LEFT";
	private static final String CMD_ILLEGAL = "ILLEGAL";
	
	//Chat capability
	private static final String CMD_CHAT_MSG = "CHAT_MSG";
}
