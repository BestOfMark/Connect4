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

	private Socket sock;
	public final int id;
	
	public String username;
	public PlayerState state = PlayerState.IDLE;
	private HostedGame game;
	private InputHandler ih;
	private BufferedWriter bw;
	public Chip chip;
	
	private int transgressions = 0;
	private static final int TRANSGRESSION_THRESHOLD = 10;
	
	public NetworkPlayer(int id, Socket sock, Server server) {
		this.id = id;
		this.sock = sock;
		username = "GUEST" + id;
		try {
			ih = new InputHandler(this, sock, server, game);
			ih.start();
		} catch (IOException e) {
			System.err.println("Error while setting up client input stream");
			state = PlayerState.ERRORED;
		}
		try {
			bw = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
		} catch (IOException e) {
			System.err.println("Error while setting up client output stream");
			state = PlayerState.ERRORED;
		}
	}
	
	public void newTransgression() {
		if (transgressions++ >= TRANSGRESSION_THRESHOLD) {
			state = PlayerState.BANNED;
			ih.close();
			game.playerBanned(this, "Banned because of too many illegal commands");
		}
	}
	
	public void enroll(HostedGame game) {
		this.game = game;
		state = PlayerState.IN_GAME;
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
	
	private void sendToClient(String cmd) {
		new Thread(new Runnable() {
			@Override
			public void run() {
				sendToClient(cmd, 0);
				
			}
		}).start();;
	}
	
	private final ReentrantLock sendLock = new ReentrantLock();
	private static final int SEND_TRIES = 4;
	private static final int SEND_INTERVAL = 10;
	synchronized private void sendToClient(String cmd, int tryCount) {
		try {
			sendLock.lock();
			try {
				bw.write(cmd);
			} finally {
				sendLock.unlock();
			}
		} catch (IOException e) {
			System.err.println("Error while sending command to " + this.toString());
			if (tryCount < SEND_TRIES) {
				System.err.println("Retrying to send command...");
				try {
					Thread.sleep(SEND_INTERVAL);
					sendToClient(cmd, tryCount++);
				} catch (InterruptedException e1) {}
			} else {
				System.err.println("Failed to contact " + this.toString());
				state = PlayerState.ERRORED;
				ih.close();
				try {
					sock.close();
				} catch (IOException e1) {}
			}
		}
	}
}
