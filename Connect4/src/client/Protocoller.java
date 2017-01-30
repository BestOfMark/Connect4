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
	
	/**
	 * Tries to set up a connection with a server specified in the <code>String</code> addressAndPort. If the server exists and responds it will
	 * setup and InputHandler and BufferedWriter.
	 * @param client The <code>client</code> object that utilizes this <code>Protocoller</code>.
	 * @param addressAndPort a <code>String<code> containing the address and port number of a server.
	 * @throws MalFormedServerAddressException
	 * @throws ServerNotFoundException
	 * @throws ServerCommunicationException
	 */
	//@ requires client != null;
	public Protocoller(Client client, String addressAndPort) throws MalFormedServerAddressException, ServerNotFoundException, ServerCommunicationException {
		this.client = client;
		try {
			String[] parts = addressAndPort.split("[:\\s]");
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
		bw.newLine();
		bw.flush();
		bw.write(String.join(COMMAND_DELIMITER, CLIENT_REQUEST));
		bw.newLine();
		bw.flush();
	}

	@Override
	public void cmdMove(int x, int y) throws IOException {
		bw.write(String.join(COMMAND_DELIMITER, CLIENT_MOVE, String.valueOf(x), String.valueOf(y)));
		bw.newLine();
		bw.flush();
	}

	@Override
	public void cmdChat(String msg) throws IOException {
		System.out.println("sending chat protocoller");
		bw.write(String.join(COMMAND_DELIMITER, CLIENT_CHAT, msg));
		bw.newLine();
		bw.flush();
	}
	
	public static final String CLIENT_HELLO = "HELLO";
	public static final String CLIENT_MOVE = "MOVE";
	public static final String CLIENT_CHAT = "CHAT";
	public static final String CLIENT_REQUEST = "REQUEST";
	
	/**
	 * Closes the communication with the server.
	 */
	public void close() {
		ih.isCloseRequested = true;
		try {
			sock.close();
		} catch (IOException e) {
			client.getView().internalMessage(e.getMessage());
		}
	}

	private class InputHandler extends Thread {
		
		private BufferedReader br;
		private boolean isCloseRequested = false;
		
		public InputHandler() throws IOException {
			br = new BufferedReader(new InputStreamReader(sock.getInputStream()));
			
		}
		
		/**
		 * Listens to input from the server. This function will only return when <code>isCloseRequested</code> is set to <code>true</code>;
		 */
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
				
				try {
					if (!isCloseRequested){
						client.getView().internalMessage("Error in Protocol.InputHandler. Trying to restore...");
						(ih = new InputHandler()).start();
					}
				} catch (IOException e1) {
					client.getView().internalMessage(e.getMessage());
				}
			}
		}
	}

	private static final String EXCEPTION_SOURCE_NAME = "Server";
	
	/**
	 * Splits the message of the server to find commands given by the server. Throws and CommandFormatException when the received
	 * input does not match any known formats of <code>Protocoller</code>
	 * @param input <code>String</code> received from the server
	 * @throws CommandFormatException
	 */
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
			input = input.substring(SERVER_LEFT.length()).trim();
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
