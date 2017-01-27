package server;

import static client.Protocoller.*;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.Socket;
import java.util.Timer;
import java.util.TimerTask;

import client.CommandFormatException;

public class InputHandler extends Thread {
	
	private BufferedReader br;
	private boolean isCloseRequested = false;
	
	private final NetworkPlayer player;
	private final Server server;
	private final HostedGame game;
	
	private int dos = 0;
	private static final int DOS_THRESHOLD = 20;
	
	public InputHandler(NetworkPlayer player, Socket sock, Server server, HostedGame game) throws IOException {
		this.player = player;
		this.server = server;
		this.game = game;
		br = new BufferedReader(new InputStreamReader(sock.getInputStream()));
		//DOS decrementer;
		Timer t = new Timer();
		t.schedule(new TimerTask() {
			@Override
			public void run() {
				updateRequests(-1);
			}
		}, 10);
	}
	
	synchronized private void updateRequests(int i) {
		dos += i;
		if (dos < 0) dos = 0;
		else if (dos >= DOS_THRESHOLD) {
			close();
			if (player.state == PlayerState.IN_GAME) {
				game.playerBanned(player, "Banned because of too many requests");
			}
			player.state = PlayerState.BANNED;
		}
	}
	
	public void close() {
		isCloseRequested = true;
	}
	
	@Override
	public void run() {
		String input;
		try {
			while (!isCloseRequested && (input = br.readLine()) != null) {
				System.out.println(player.username + "(" + player.id + "): " + input);
				updateRequests(1);
				try {
					parse(input);
				} catch (CommandFormatException e) {
					System.err.println(e.getMessage());
				}
			}
		} catch (IOException e) {
			player.state = PlayerState.ERRORED;
			System.err.println("The inputhandler of " + player.toString() + " errored");
		}
		System.out.println("Closing the inputhandler of " + player.toString());
	}
	
	private static final String EXCEPTION_SOURCE_NAME = "Client";
	public void parse(String input) throws CommandFormatException {
		if (input.startsWith(CLIENT_HELLO)) {
			input = input.substring(CLIENT_HELLO.length()).trim();
			String[] args = input.split(COMMAND_DELIMITER);
			try {
				server.hello(
					player,
					args[0],
					Boolean.parseBoolean(args[1]),
					Integer.parseInt(args[2]));
			} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
				throw new CommandFormatException(CLIENT_HELLO, input, EXCEPTION_SOURCE_NAME);
			}
		} else if (input.startsWith(CLIENT_MOVE)) {
			if (!(player.state == PlayerState.IN_GAME)) {
				player.cmdReportIllegal(input);
				player.newTransgression();
			}
			input = input.substring(CLIENT_MOVE.length()).trim();
			String[] args = input.split(COMMAND_DELIMITER);
			try {
				game.moveReceived(
					player,
					Integer.parseInt(args[0]),
					Integer.parseInt(args[1]));
			} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
				throw new CommandFormatException(CLIENT_MOVE, input, EXCEPTION_SOURCE_NAME);
			}
		} else if (input.startsWith(CLIENT_CHAT)) {
			input = input.substring(CLIENT_CHAT.length()).trim();
			String[] args = input.split(COMMAND_DELIMITER);
			try {
				server.chatReceived(
					player,
					Integer.parseInt(args[0]),
					args[1]);
			} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
				throw new CommandFormatException(CLIENT_CHAT, input, EXCEPTION_SOURCE_NAME);
			}
		} else {
			player.cmdReportIllegal(input);
			player.newTransgression();
		}
	}
}