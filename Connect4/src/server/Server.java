package server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Random;

public class Server {
	
	/**
	 * Maps all players, that are connected or have been connected to the server, 
	 * to their given (unique) id's.
	 */
	private HashMap<Integer, NetworkPlayer> connectedPlayers;
	
	/**
	 * Keeps track of all games that are hosted on the server.
	 */
	private ArrayList<HostedGame> games;
	
	/**
	 * This variable keeps track of which id is available for a new client/user. Every time 
	 * a new client connects he is given this id and afterwards the value is incremented by one.
	 */
	//@ invariant connectedPlayers.size == idCount;
	private int idCount = 0;
	
	/**
	 * Reference to this server's <code>Porter</code> object/thread.
	 */
	private Porter porter;
	
	/**
	 * Initialize the server.
	 */
	public Server() {
		//Initialize the collections
		connectedPlayers = new HashMap<>();
		games = new ArrayList<>();
		
		//Spawn the thread that will listen for new connections.
		try {
			porter = new Porter(this);
			porter.start();
		} catch (IOException e) {
			System.err.println("Failed setting up a server socket");
		}
	}
	
	/**
	 * Add a new <code>NetworkPlayer</code> to the currently connected players list.
	 * @param player the new player.
	 */
	//@ requires player != null;
	//@ ensures connectedPlayers.get(player.id) == player;
	private void addPlayer(NetworkPlayer player) {
		connectedPlayers.put(player.id, player);
		System.out.println(player.toString() + " connected");
	}
	
	/**
	 * Find a player that is available for a match. The returned player will not be the same as the 
	 * player passed as an argument. An available player is picked at random from all connected 
	 * players.
	 * @param requester the <code>NetworkPlayer</code> that is looking for an opponent.
	 * @return a <code>NetworkPlayer</code> that is available for matchmaking.
	 */
	//@ requires requester != null;
	//@ ensures \result != requester;
	/*@ pure */ private NetworkPlayer getAvailableOpponent(NetworkPlayer requester) {
		/* The list of connected players will be iterated over randomly. 
		 * For this purpose a random permutation of size idCount is
		 * created. This corresponds to the number of connected players.*/
		int[] randperm = randperm(idCount);
		for (int i = 0; i < randperm.length; i++) {
			NetworkPlayer player = connectedPlayers.get(randperm[i]);
			//Check if the player is available
			if (player != null && !player.equals(requester) && 
					player.state == PlayerState.WAITING) {
				return player;
			}
		}
		return null;
	}
	
	/**
	 * Close the <code>Porter</code>, such that the server cannot listen for new connections 
	 * anymore.
	 */
	public void close() {
		porter.isCloseRequested = true;
		Iterator<Integer> it = connectedPlayers.keySet().iterator();
		while (it.hasNext()) {
			NetworkPlayer player = connectedPlayers.get(it.next());
			player.close();
		}
	}
	
	/**
	 * Create an array that stores a random permutation of the set [0, <b>size</b>-1].
	 * @param size the size of the random permutation array.
	 * @return the random permutation
	 */
	//@ requires size >= 0;
	//@ ensures \result.length == size;
	/*@ pure */ private static int[] randperm(int size) {
		//Fill a list with integers from 0 to size-1
		ArrayList<Integer> availableInts = new ArrayList<>();
		for (int i = 0; i < size; i++) {
			availableInts.add(i);
		}
		
		//Randomly pick integers from the list and store them in the array
		int[] randperm = new int[availableInts.size()];
		int index = 0;
		Random rand = new Random();
		while (!availableInts.isEmpty()) {
			randperm[index++] = availableInts.remove(rand.nextInt(availableInts.size()));
		}
		
		//Check if the JML contract is honoured.
		assert randperm.length == size;
		return randperm;
	}
	
	/**
	 * The <code>Porter</code> listens for new connections and creates a new <code>NetworkPlayer
	 * </code> object when a client connects to the server.
	 */
	private class Porter extends Thread {
		
		/**
		 * The port to which the server is connected.
		 */
		private static final int PORT = 666;
		
		/**
		 * Stores the <code>Server</code> object, which should be passed to the constructor of 
		 * <code>NetworkPlayer</code>.
		 */
		private final Server server;
		
		/**
		 * The <code>ServerSocket</code> object.
		 */
		private ServerSocket ss;
		
		/**
		 * If this variable is set to <code>true</code> then the <code>run()</code> method will 
		 * break from the <code>while</code>-loop in the next iteration. Consequently, the <code>
		 * Porter</code> thread finishes and the server will no longer listen for new connections.
		 */
		private boolean isCloseRequested = false;
		
		/**
		 * Construct the <code>Porter</code> object and open a server socket.
		 * @param server the <code>ServerSocket</code> object to which this <code>Porter</code> 
		 * is associated.
		 * @throws IOException when something goes wrong while opening the server socket.
		 */
		public Porter(Server server) throws IOException {
			this.server = server;
			ss = new ServerSocket(PORT);
		}
		
		/**
		 * Listens for new connections and when a new connection is made, reports to the server with
		 * a new <code>NetworkPlayer</code>. This method will not return unless <code>close()</code>
		 * is called from the <code>Server</code> class.
		 */
		@Override
		public void run() {
			try {
				while (!isCloseRequested) {
					Socket sock = ss.accept();
					//Create a new player with an available id, and then increment the id to be used
					//for the next player.
					addPlayer(new NetworkPlayer(idCount++, sock, server));
				}
			} catch (IOException e) {
				System.err.println("Error while accepting client socket");
			}
			System.out.println("Porter exiting...");
		}
	}
	
	/**.
	 * The main method for the Server application
	 * @param args array of command line arguments. See ARGS_MSG for the required arguments
	 */
	public static void main(String[] args) {
//		args = new String[]{"4", "4", "4", "4", "60000"};
		if (args.length == 5) {
			//Parse the arguments
			try {
				dimX = Integer.parseInt(args[0]);
				dimY = Integer.parseInt(args[1]);
				dimZ = Integer.parseInt(args[2]);
				winLength = Integer.parseInt(args[3]);
				thinkTime = Integer.parseInt(args[4]);
			} catch (NumberFormatException e) {
				//One or more argument is not a number
				System.out.println(NOT_A_NUMBER);
				return;
			}
		} else {
			//Not enough arguments
			System.out.println(ARGS_MSG);
			return;
		}
		//If something was wrong with the program arguments, 
		//the method should have already returned.
		new Server();
	}

	private static final String ARGS_MSG = 
			"Usage: [x-dimension] [y-dimension] [z-dimension] [win-length] [thinking time (in ms)]";
	private static final String NOT_A_NUMBER = "Arguments must be numbers";
	public static int dimX, dimY, dimZ, winLength;
	public static int thinkTime = 60000;
	private static final int MAGIC_NUMBER = 0;
	
	/**
	 * Called when the <code>InputHandler</code> of a <code>NetworkPlayer</code> receives a 
	 * <b>HELLO</b> command. The player is welcomed with the WELCOME command.
	 * @param player the <code>NetworkPlayer</code> from which this command originated.
	 * @param username the desired username of the player.
	 * @param isAI <code>true</code> indicates that the user that is registering is a computer
	 * player. <code>false</code> indicates a human player.
	 * @param magicNumber the supported capabilities of the client.
	 */
	public void hello(NetworkPlayer player, String username, boolean isAI, int magicNumber) {
		player.username = username;
		player.cmdWelcome(player.id, thinkTime, MAGIC_NUMBER);
		player.state = PlayerState.IDLE;
	}
	
	/**
	 * Called when the <code>InputHandler</code> of a <code>NetworkPlayer</code> receives a 
	 * <b>REQUEST</b> command. The server will try to find an opponent for that player. If no 
	 * opponent is available the player will be available to be matched when another client sends
	 * the request command.
	 * @param player the player that made the request
	 */
	public void gameRequested(NetworkPlayer player) {
		player.state = PlayerState.WAITING;
		//Looking for an opponent
		NetworkPlayer opponent = getAvailableOpponent(player);
		if (opponent != null) {
			//Opponent found, starting new game
			HostedGame game = new HostedGame(this, player, opponent, dimX, dimY, dimZ, winLength);
			games.add(game);
			System.out.println("Opponent found for " + player.toString());
		} else {
			//Currently no opponent
			System.out.println("No player found for " + player.toString());
		}
	}

	/**
	 * Called when the <code>InputHandler</code> of a <code>NetworkPlayer</code> receives a <b>CHAT
	 * </b> command. Broadcasts the chat message to every connected client, that is not banned or 
	 * errored.
	 * @param msg the message to be sent
	 */
	public void chatReceived(NetworkPlayer player, String msg) {
		//Send to everyone, including the sender
		Iterator<Integer> it = connectedPlayers.keySet().iterator();
		while (it.hasNext()) {
			NetworkPlayer np = connectedPlayers.get(it.next());
			//Send only if the player is still active on the server
			if (np.state == PlayerState.IDLE || np.state == PlayerState.IN_GAME || 
					np.state == PlayerState.WAITING) {
				np.cmdBroadcastMessage(player.id, msg);
			}
		}

	}

}
