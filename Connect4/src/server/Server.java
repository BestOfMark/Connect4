package server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Random;

import client.Protocoller;

public class Server {
	
	private HashMap<Integer, NetworkPlayer> connectedPlayers;
	private ArrayList<HostedGame> games;
	
	private int idCount = 0;
	
	public Server() {
		connectedPlayers = new HashMap<>();
		games = new ArrayList<>();
		
		try {
			(new Porter(this)).start();
		} catch (IOException e) {
			System.err.println("Failed setting up a server socket");
		}
	}
	
	private void addPlayer(NetworkPlayer player) {
		connectedPlayers.put(player.id, player);
		System.out.println(player.toString() + " connected");
	}
	
	private NetworkPlayer getIdlePlayer(NetworkPlayer requester) {
		int[] randperm = randperm(idCount);
		for (int i = 0; i < randperm.length; i++) {
			NetworkPlayer player = connectedPlayers.get(randperm[i]);
			if (player != null && !player.equals(requester) && player.state == PlayerState.IDLE) return player;
		}
		return null;
	}
	
	private static int[] randperm(int size) {
		ArrayList<Integer> availableInts = new ArrayList<>();
		for (int i = 0; i < size; i++) {
			availableInts.add(i);
		}
		int[] randperm = new int[availableInts.size()];
		int index = 0;
		Random rand = new Random();
		while (!availableInts.isEmpty()) {
			randperm[index++] = availableInts.remove(rand.nextInt(availableInts.size()));
		}
		return randperm;
	}
	private class Porter extends Thread {
		
		private static final int PORT = 666;
		private final Server server;
		private ServerSocket ss;
		
		public Porter(Server server) throws IOException {
			this.server = server;
			ss = new ServerSocket(PORT);
		}
		
		@Override
		public void run() {
			try {
				Socket sock = ss.accept();
				addPlayer(new NetworkPlayer(idCount++, sock, server));
				
			} catch (IOException e) {
				System.err.println("Error while accepting client socket");
			}
		}
	}
	
	public static void main(String[] args) {
		new Server();
	}

	public void hello(NetworkPlayer player, String username, boolean isAI, int magicNumber) {
		player.username = username;
		NetworkPlayer opponent = getIdlePlayer(player);
		if (opponent != null) {
			HostedGame game = new HostedGame(this, player, opponent);
			games.add(game);
			System.out.println("Opponent found for " + player.toString());
		} else {
			System.out.println("No player found for " + player.toString());
		}
	}

	public void chatReceived(NetworkPlayer player, int recipientId, String msg) {
		NetworkPlayer recipient = connectedPlayers.get(recipientId);
		if (recipient == null) {
			player.cmdReportIllegal(String.join(Protocoller.COMMAND_DELIMITER, String.valueOf(recipientId), msg));
		} else {
			recipient.cmdBroadcastMessage(player.id, msg);
			player.cmdBroadcastMessage(player.id, msg);
		}
	}

}
