package server;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.concurrent.locks.ReentrantLock;

import game.Chip;
import server.protocol.ChatCapabilityServer;
import server.protocol.Connect4Server;

import static client.Protocoller.*;

public class NetworkPlayer implements Connect4Server, ChatCapabilityServer {

	/**
	 * The socket through which this player connected.
	 */
	//@ invariant sock != null;
	private final Socket sock;
	
	//Specific user data
	public final int id;
	public String username;
	public Chip chip;
	
	/**
	 * If this player is in a game this variable will reference that game.
	 */
	//@ invariant state = PlayerState.IN_GAME ==> game != null;
	private HostedGame game;
	
	/**
	 * The state this player is currently in
	 */
	public PlayerState state = PlayerState.UNKNOWN;
	
	//input/output
	private InputHandler ih;
	private BufferedWriter bw;
	
	/**
	 * Counter for the transgressions of this player. The player is banned if this value is equal to the <code>TRANSGRESSION_THRESHOLD</code>.
	 */
	private int transgressions = 0;
	
	/**
	 * Stores the threshold for banning this player.
	 */
	private static final int TRANSGRESSION_THRESHOLD = 10;
	
	/**
	 * Construct a new <code>NetworkPlayer</code>.
	 * @param id the id assigned to this player
	 * @param sock the socket on which this player connected to the server
	 * @param server reference to the <code>Server</code> object that creates this player
	 */
	public NetworkPlayer(int id, Socket sock, Server server) {
		this.id = id;
		this.sock = sock;
		username = "GUEST" + id;
		
		//Launch this player's inputhandler
		try {
			ih = new InputHandler(this, sock, server);
			ih.start();
		} catch (IOException e) {
			System.err.println("Error while setting up client input stream");
			state = PlayerState.ERRORED;
		}
		
		//Set up the output writer
		try {
			bw = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
		} catch (IOException e) {
			System.err.println("Error while setting up client output stream");
			state = PlayerState.ERRORED;
		}
	}
	
	/**
	 * Increment the transgression counter of this player. If the threshold is reached the player will be banned and
	 * the server will no longer listen to this player. If the player is currently in-game the <code>HostedGame</code>
	 * object is notified.
	 */
	public void newTransgression() {
		//Increment the transgressions counter and check if the threshold is reached.
		if (++transgressions >= TRANSGRESSION_THRESHOLD) {
			//Ban the player
			state = PlayerState.BANNED;
			ih.close();
			System.out.println(this.toString() + ": " + MSG_BANNED_ILLEGAL);
			
			//Let the game know this player has been banned
			if (game != null) {
				game.playerLeft(this, MSG_BANNED_ILLEGAL);
			}
		}
	}
	
	/**
	 * Set the game reference of this <code>NetworkPlayer</code> object and of its input handler. In addition, the player's state is updated to
	 * in-game.
	 * @param game the game this player will be enrolled in
	 */
	public void enroll(HostedGame game) {
		this.game = game;
		ih.setGame(game);
		state = PlayerState.IN_GAME;
	}
	
	/**
	 * Set the game reference of this <code>NetworkPlayer</code> object and of its input handler to null. The player's state is set to IDLE.
	 * @param game the game from which this player is disenrolled
	 */
	public void disenroll(HostedGame game) {
		this.game = null;
		ih.setGame(null);
		state = PlayerState.IDLE;
	}
	
	@Override
	public String toString() {
		return "NetworkPlayer{id = " + id + ", name = " + username + ", socket = " + sock.toString() + "}";
	}

	@Override
	public void cmdWelcome(int assignedUserID, long allowedThinkTime, int capabilities) {
		sendToClient(String.join(COMMAND_DELIMITER, SERVER_WELCOME, 
				String.valueOf(assignedUserID), 
				String.valueOf(allowedThinkTime), 
				String.valueOf(capabilities)));
	}

	@Override
	public void cmdGame(String nameOtherPlayer, int otherPlayerID, int playFieldX, int playFieldY, int playFieldZ,
			int playerWhoHasNextTurnID, int sequenceLengthOfWin) {
		sendToClient(String.join(COMMAND_DELIMITER, SERVER_GAME,
				nameOtherPlayer,
				String.valueOf(otherPlayerID),
				String.valueOf(playFieldX),
				String.valueOf(playFieldY),
				String.valueOf(playFieldZ),
				String.valueOf(playerWhoHasNextTurnID),
				String.valueOf(sequenceLengthOfWin)));
	}

	@Override
	public void cmdMoveSuccess(int moveX, int moveY, int actorID, int playerWhoHasNextTurnID) {
		sendToClient(String.join(COMMAND_DELIMITER, SERVER_MOVE_SUCCESS, 
				String.valueOf(moveX), 
				String.valueOf(moveY), 
				String.valueOf(actorID), 
				String.valueOf(playerWhoHasNextTurnID)));
	}

	@Override
	public void cmdGameEnd(int winnerID) {
		sendToClient(String.join(COMMAND_DELIMITER, SERVER_GAME_END, 
				String.valueOf(winnerID)));
	}

	@Override
	public void cmdReportIllegal(String theIllegalCommandWithParameters) {
		sendToClient(String.join(COMMAND_DELIMITER, SERVER_ILLEGAL, 
				theIllegalCommandWithParameters));
	}

	@Override
	public void cmdPlayerLeft(int leftPlayerID, String reason) {
		sendToClient(String.join(COMMAND_DELIMITER, SERVER_LEFT, 
				String.valueOf(leftPlayerID), 
				reason));
	}

	@Override
	public void cmdBroadcastMessage(int senderId, String msg) {
		sendToClient(String.join(COMMAND_DELIMITER, SERVER_CHAT_MSG, 
				String.valueOf(senderId), 
				msg));
	}
	
	/**
	 * Launch a thread that will try to send a command to the client of this player. The command is not sent if the player is banned or an error has occurred
	 * earlier.
	 * @param cmd the command to be sent.
	 */
	private void sendToClient(String cmd) {
		if (state == PlayerState.BANNED || state == PlayerState.ERRORED) return;
		new Thread(new Runnable() {
			@Override
			public void run() {
				sendToClient(cmd, 0);
				
			}
		}).start();;
	}
	
	/**
	 * This lock is used to ensure that only one command is sent to the client at a time.
	 */
	private final ReentrantLock sendLock = new ReentrantLock();
	
	/**
	 * The amount of attempts that will be made to send this command;
	 */
	private static final int SEND_TRIES = 4;
	
	/**
	 * The thread that tries to send the command will wait for this specified amount of time (in milliseconds) before it tries to send again.
	 */
	private static final int SEND_INTERVAL = 10;
	
	/**
	 * <b>This method should only be called internally. To send a command use <code>sendToClient(String cmd)</code></b><br><br>
	 * Send a command to the client. If, for some reason, an error occurs while sending the command, the method is called recursively in order 
	 * to try and send the command again. After a certain amount of tries it gives up and the player's state is set to ERRORED.
	 * @param cmd the command to send.
	 * @param tryCount the amount of tries already made to send the command
	 */
	synchronized private void sendToClient(String cmd, int tryCount) {
		try {
			sendLock.lock();
			try {
				//Send the command
				bw.write(cmd);
				bw.newLine();
				bw.flush();
				System.out.println("Command sent: " + cmd);
			} finally {
				sendLock.unlock();
			}
		} catch (IOException e) {
			//Sending the command errored
			System.err.println("Error while sending command to " + this.toString());
			//Check how many tries have been made to send the command
			if (tryCount++ < SEND_TRIES) {
				//Will retry to send it
				System.err.println("Retrying to send command...");
				try {
					Thread.sleep(SEND_INTERVAL);
					sendToClient(cmd, tryCount++);
				} catch (InterruptedException e1) {}
			} else {
				//Give up on sending the command and set the state to errored
				System.err.println(this.toString() + ": " + MSG_ERRORED);
				state = PlayerState.ERRORED;
				if (state == PlayerState.IN_GAME) game.playerLeft(this, MSG_ERRORED); 
				//Close the handlers of this player
				try {
					bw.close();
				} catch (IOException e2) {
					e2.printStackTrace();
				}
				ih.close();
				try {
					sock.close();
				} catch (IOException e1) {}
			}
		}
	}
	
	/**
	 * Message sent to opponent (if in-game) and written to the console when this player gets banned because of too many illegal commands. 
	 */
	public static final String MSG_BANNED_ILLEGAL = "Banned because of too many illegal commands";
	
	/**
	 * Message sent to opponent (if in-game) and written to the console when this player gets banned because of too many requests. 
	 */
	public static final String MSG_BANNED_REQUESTS = "Banned because of too many requests to the server";
	
	/**
	 * Message sent to opponent (if in-game) and written to the console when this player errors. 
	 */
	public static final String MSG_ERRORED = "Failed to contact this player";
}
