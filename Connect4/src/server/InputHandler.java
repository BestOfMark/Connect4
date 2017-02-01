package server;

import static client.Protocoller.*;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.Socket;
import java.util.Timer;
import java.util.TimerTask;

import client.Client;
import client.CommandFormatException;

public class InputHandler extends Thread {
	
	/**
	 * The reader used to read the incoming commands.
	 */
	private BufferedReader br;
	
	/**
	 * Reference to the associated player.
	 */
	private final NetworkPlayer player;
	
	/**
	 * Reference to the <code>Server</code> object.
	 */
	private final Server server;
	
	/**
	 * If the associated player is in-game then this is a reference to the game the player is 
	 * involved in.
	 */
	//@invariant player.state == PlayerState.IN_GAME ==> game != null;
	private HostedGame game;
	
	/**
	 * Denial of Service (DoS) counter. Keeps track of the amount of requests the client has send 
	 * in a short amount of time. If the amount exceeds a certain threshold the client is given a 
	 * denial of service, in this case the server will not listen to it anymore. Every so often the 
	 * value is decremented such that the denial of service is only given if the client makes many 
	 * requests in a short amount of time.
	 */
	//@ invariant dos >= 0;
	private int dos = 0;
	
	/**
	 * If this threshold is reached the player will be banned for sending too many requests in a 
	 * short amount of time.
	 */
	private static final int DOS_THRESHOLD = Integer.MAX_VALUE;
	
	/**
	 * The Denial of Service counter is decremented every this amount of milliseconds. A client 
	 * should not send requests faster than this rate
	 * or it might get banned from the server.
	 */
	private static final int DOS_DECREMENT_INTERVAL = 1;
	
	/**
	 * Construct a player's input handler, which listens to commands send from the client to the 
	 * server.
	 * @param player the player whose input handler this is
	 * @param sock the socket through which the player is connected
	 * @param server reference to the server the player is connected to
	 * @throws IOException if the input reader could not be opened
	 */
	//@ requires player != null
	//@ requires sock != null
	//@ requires server != null
	public InputHandler(NetworkPlayer player, Socket sock, Server server) throws IOException {
		this.player = player;
		this.server = server;
		br = new BufferedReader(new InputStreamReader(sock.getInputStream()));
		
		//DOS decrementer;
		Timer t = new Timer();
		t.schedule(new TimerTask() {
			@Override
			public void run() {
				updateRequests(-1);
			}
		}, DOS_DECREMENT_INTERVAL);
	}
	
	/**
	 * Sets the <code>HostedGame</code> reference of the input handler.
	 * @param game the game the associated player is involved in
	 */
	public void setGame(HostedGame game) {
		this.game = game;
	}

	/**
	 * Adds a certain value to the DoS counter.
	 * @param val the DoS counter is increased with this value. Supposed to be positive, with an 
	 * exception for the DoS decrementer thread.
	 */
	synchronized private void updateRequests(int val) {
		dos += val;
		//Keep the DoS counter positive
		if (dos < 0) {
			dos = 0;
		} else if (dos >= DOS_THRESHOLD) {
			//Ban the player if the threshold is reached
			close();
			System.out.println(player.toString() + ": " + NetworkPlayer.MSG_BANNED_REQUESTS);
			if (player.state == PlayerState.IN_GAME) {
				//Let the opponent know
				game.playerLeft(player, NetworkPlayer.MSG_BANNED_REQUESTS);
			}
			player.state = PlayerState.BANNED;
		}
	}
	
	/**
	 * If this variable is set to <code>true</code> then the <code>run()</code> method will break 
	 * from the <code>while</code>-loop in the next iteration. Consequently, the <code>InputHandler
	 * </code> thread finishes and the server will no longer listen to the associated client.
	 */
	private boolean isCloseRequested = false;
	
	/**
	 * Close this input handler. The server will no longer listen to the associated client.
	 */
	public void close() {
		isCloseRequested = true;
	}
	
	/**
	 * Listens for commands from the client.
	 */
	@Override
	public void run() {
		String input;
		try {
			while (!isCloseRequested) {
				input = br.readLine();
				if (input == null) {
					return;
				}
				//Command received
				System.out.println(player.username + "(" + player.id + "): " + input);
				updateRequests(1);
				try {
					//Parse the command
					parse(input);
				} catch (CommandFormatException e) {
					//The command could not be passed. Counts as a transgression for the player.
					System.err.println(e.getMessage());
					player.cmdReportIllegal(input);
					player.newTransgression();
				}
			}
		} catch (IOException e) {
			//The inputstream errored
			if (player.state == PlayerState.IN_GAME) {
				game.playerLeft(player, NetworkPlayer.MSG_ERRORED);
			}
			player.state = PlayerState.ERRORED;
			System.err.println("The inputhandler of " + player.toString() + " errored");
		}
		System.out.println("Closing the inputhandler of " + player.toString());
	}
	
	/**
	 * Indicates where the command was sent from. Used in exception messages.
	 */
	private static final String EXCEPTION_SOURCE_NAME = "Client";
	
	/**
	 * Parses the command and acts according to that command.
	 * @param input the full received command
	 * @throws CommandFormatException if the command's keyword is invalid and/or its arguments
	 */
	//requires input != null;
	public void parse(String input) throws CommandFormatException {
		String inputCopy = input;
		//Check for all known keywords
		if (inputCopy.startsWith(CLIENT_HELLO)) {
			//Remove the keyword from the beginning of the command
			inputCopy = inputCopy.substring(CLIENT_HELLO.length()).trim();
			//Retrieve the arguments in an array
			String[] args = inputCopy.split(COMMAND_DELIMITER);
			//Parse the arguments and call the correct method
			try {
				server.hello(
					player,
					args[0],
					Boolean.parseBoolean(args[1]),
					Integer.parseInt(args[2]));
			} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
				//One or more arguments could not be parsed so an exception is thrown
				throw new CommandFormatException(CLIENT_HELLO, inputCopy, EXCEPTION_SOURCE_NAME);
			}
		} else if (inputCopy.startsWith(CLIENT_MOVE)) {
			//From here on no more comments. The logic is the same as the preceding conditional 
			//code block
			if (!(player.state == PlayerState.IN_GAME)) {
				player.cmdReportIllegal(inputCopy);
				player.newTransgression();
			}
			inputCopy = inputCopy.substring(CLIENT_MOVE.length()).trim();
			String[] args = inputCopy.split(COMMAND_DELIMITER);
			if (game == null) {
				//Client sent a move while not in-game
				System.err.println(player.toString() + " is not in-game");
				return;
			}
			try {
				game.moveReceived(
					player,
					Integer.parseInt(args[0]),
					Integer.parseInt(args[1]));
			} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
				throw new CommandFormatException(CLIENT_MOVE, inputCopy, EXCEPTION_SOURCE_NAME);
			}
		} else if (inputCopy.startsWith(CLIENT_CHAT)) {
			inputCopy = inputCopy.substring(CLIENT_CHAT.length()).trim();
			server.chatReceived(player, inputCopy);
		} else if (inputCopy.startsWith(CLIENT_REQUEST)) {
			server.gameRequested(player);
		} else if (Client.DEBUG && inputCopy.equals("TERMINATE")) {
			//Close the server for testing
			System.exit(-1);
		} else {
			//Extract the unknown command keyword if applicable.
			int index = inputCopy.indexOf(' ');
			String unknownCommand = (index != -1) ? inputCopy.substring(0, index) : "";
			
			throw new CommandFormatException(unknownCommand, inputCopy, EXCEPTION_SOURCE_NAME);
		}
	}
}