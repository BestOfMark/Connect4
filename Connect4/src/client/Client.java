package client;

import java.awt.Point;
import java.io.IOException;

import client.player.ComputerPlayer;
import client.player.HumanPlayer;
import client.player.NaiveAI;
import client.player.Player;
import client.player.Yuno;
import client.ui.Controller;
import client.ui.GUI;
import client.ui.GUIController;
import client.ui.View;
import game.BoundedField;
import game.Chip;
import game.Field;

public class Client {

	/**
	 * Stores the <code>Controller</code> object used by the <code>Client</code>.
	 */
	private Controller control;
	
	/**
	 * Stores the <code>View</code> object used by the <code>Client</code> 
	 */
	private View view;
	
	/**
	 * Stores the <code>Field</code> object received by the server.
	 */
	private Field field;
	
	/**
	 * Stores the <code>Player</code> of the local player.
	 */
	private Player local;
	
	/**
	 * Stores the <code>Player</code> of the opponent.
	 */
	private Player enemy;
	
	/**
	 * If this variable is set to <code>true</code> it will break the while runtimeloop in the <code>Client</code>, leading to the
	 * termination of the client.
	 */
	private boolean exitRequested = false;
	
	/**
	 * Variable used to set debug messages to visible or invisible. If <code>debug</code> == <code>true</code>, the debug messages are
	 * Visible. If <code>debug</code> == <code>false</code>, the debug messages are invisible. 
	 */
	public static final boolean DEBUG = true;
	
	/**
	 * Contains the supported features of the <code>Client</code>.
	 */
	private static final int MAGIC_NUMBER = 00;
	
	/**
	 * Stores the <code>Protocoller</code> used by this <code>Client</code>.
	 */
	private Protocoller protocoller;
	
	/**
	 * This <code>enum</code> provides all the possible states used by the <code>Client</code>. 
	 *
	 */
	private enum GameState {
		UNCONNECTED, IDLE, CONNECTED, GAME_TURN, GAME_AWAITING_RESPONSE, GAME_WAIT, SHUTDOWN;
	}
	
	/**
	 * The state used to define the current state of the <code>Client</code>.
	 */
	private GameState state = GameState.UNCONNECTED;
	
	/**
	 * Initialize the client
	 */
	public Client(Player localPlayer) {
		local = localPlayer;
		control = new GUIController(this);
		view = new GUI(this);
		control.setView(view);
		control.setPlayer(local);
		view.setController(control);
	}

	/**
	 * Handles communication with the <code>Player</code> and uses a <code>Protocoller</code> to communicate with the server.
	 */
	private void runtimeLoop() {
		while (!exitRequested) {
			switch (state) {
			case UNCONNECTED:
				String address = control.requestAddress();
				if (address != null) {
					view.internalMessage("Obtained address " + address);
					try {
						protocoller = new Protocoller(this, address);
						try {
							protocoller.cmdHello(local.username, local instanceof ComputerPlayer, MAGIC_NUMBER);
							state = GameState.IDLE;
						} catch (IOException e) {
							view.internalMessage("Hello command failed");
						}
					} catch (MalFormedServerAddressException e) {
						view.internalMessage(e.getMessage());
					} catch (ServerNotFoundException e) {
						view.internalMessage(e.getMessage());
					} catch (ServerCommunicationException e) {
						view.internalMessage(e.getMessage());
					}
				}
				break;
			case IDLE:
				break;
			case CONNECTED:
				break;
			case GAME_TURN:
				Point p = control.requestMove(field.deepCopy());
				if (p != null) {
					view.internalMessage("Obtained move " + p.toString());
				} else {
					view.internalMessage("Turn timed out");
					//What happens next
					break;
				}
				if (!field.inBounds(p.x, p.y) || field.columnFull(p.x, p.y)) {
					if (local instanceof ComputerPlayer) {
						p = new Point(0,0);
					} else {
						view.internalMessage("Invalid move");
						break;
					}
				}
				try {
					protocoller.cmdMove(p.x, p.y);
				} catch (IOException e) {
					view.internalMessage("Error while sending move");
					protocoller.close();
					state = GameState.UNCONNECTED;
				}
				state = GameState.GAME_AWAITING_RESPONSE;
				break;
			case GAME_AWAITING_RESPONSE:
				break;
			case GAME_WAIT:
				break;
			case SHUTDOWN:
				exitRequested = true;
				break;
			}
		}
	}
	
	/**
	 * Sets the timeout time, the features of the game, the usedID of the <code>Player</code>.
	 * @param userID userID that was received by the server
	 * @param millis the allowed time to respond to the server before
	 * @param magicNumber an integer containing all the features of the game. 
	 */
	//@ requires milles > 0;
	protected void welcomed(int userID, int millis, int magicNumber) {
		control.setTimeout(millis);
		local.setId(userID);
		state = GameState.CONNECTED;
	}
	
	/**
	 * starts a new game
	 * @param enemyName  Name of the enemy <code>Player</code>.
	 * @param enemyID    ID of the enemy <code>Player</code>.
	 * @param boardSizeX length of the board in the x-dimension.
	 * @param boardSizeY length of the board in the y-dimension.
	 * @param boardSizeZ length of the board in the z-dimension.
	 * @param startingPlayer the ID of the <code>Player</code> that will make the first move.
	 * @param winLength specifies the length of chips needed to win the game.
	 */
	//@ requires boardSizeX > 0; boardSizeY > 0; boardSizeZ > 0; winLength > 1;
	//@ requires boardSizeX >= winLength || boardSizeY >= winLength || boardSizeZ >= winlength;
	//@ requires enemyID != userID;
	protected void newGame(String enemyName, int enemyID, int boardSizeX, int boardSizeY, int boardSizeZ, int startingPlayer, int winLength) {
		enemy = new HumanPlayer(enemyName, local.chip.other());
		enemy.setId(enemyID);
		field = new BoundedField(boardSizeX, boardSizeY, boardSizeZ, winLength);
		field.addObserver(view);
		getView().internalMessage("Game started");
		getView().internalMessage("Your opponent: " + enemyName);
		getView().internalMessage("ID of your opponent: " + enemyID);
		getView().internalMessage("X-Dimension of the board " + boardSizeX);
		getView().internalMessage("Y-Dimension of the board " + boardSizeY);
		getView().internalMessage("Z-Dimension of the board " + boardSizeZ);
		getView().internalMessage("Length to win " + winLength);
		if (startingPlayer == enemyID) {
			state = GameState.GAME_WAIT;
		} else {
			state = GameState.GAME_TURN; 			
		}
		System.out.println(field.toString());
		view.update(field, "START");
	}
	
	/**
	 * Will display the received chat on the used <code>View</code> with the playerID or the user name of the opponent when the ID
	 * matches the ID of the opponent.
	 * @param sendId ID of the sending <code>Player</code>.
	 * @param msg <code>String</code> containing the message that was send by the sending <code>Player</code>.
	 */
	//@ requires enemyID != userID;
	public void chatReceived(int sendId, String msg) {
		if (enemy != null && sendId == enemy.getId()) {
			view.chatMessage(enemy.username + ": " + msg);
		} else if (sendId == local.getId()) {
			view.chatMessage("Me: " + msg);
		} else {
			view.chatMessage(sendId + ": " + msg);
		}
	}

	/**
	 * Is called when an illegal move was made. Will display the input on the used <code>View</code> and will disconnect from the server 
	 * if the <code>Player</code> is an instance of <code>ComputerPlayer</code> and the input contains the String move.  
	 * @param input <code>String</code> containing the send illegal command.
	 */
	public void illegalCommand(String input) {
		view.internalMessage(input);
		if (input.contains(Protocoller.CLIENT_MOVE)) {
			if (local instanceof ComputerPlayer) state = GameState.UNCONNECTED;
		}
	}

	/**
	 * Called when the enemy <code>Player</code> disconnects from the game.
	 * @param enemyID ID of the enemy <code>Player</code>
	 * @param string message received when the opponent left the game.
	 */
	public void opponentLeft(int enemyID, String string) {
		view.internalMessage(string);
		state = GameState.CONNECTED;
	}

	/**
	 * Gives a message informing the <code>Player</code> whether the game ended in a win, loss or a tie. 
	 * @param id The Id of the winning player.
	 */
	public void gameOver(int id) {
		if (id == local.getId()) {
			view.internalMessage("You have won the game");
		} else if (id == enemy.getId()) {
			view.internalMessage("You have lost the game");
		} else if (id == -1) {
			view.internalMessage("The game has ended in a tie");
		} else {
			view.internalMessage("Weird ID received");			
		}
		view.update(field, "END");
		state = GameState.CONNECTED;
	}

	/**
	 * Adds a chip to the <code>field</code> as received by the server.
	 * @param x location in the x-dimension of the field.
	 * @param y location in the y-dimension of the field
	 * @param moveId ID of the <code>Player</code> whom made the move.
	 * @param nextId ID of the <code>Player</code> whom has to make the next move.
	 */
	public void receivedMove(int x, int y, int moveId, int nextId) {
		getView().internalMessage("x-pos of the move: " + x);
		getView().internalMessage("y-pos of the move: " + y);
		getView().internalMessage("Move made by ID: "  + moveId);
		getView().internalMessage("Next playerID to make a move: " + nextId);
		if (moveId == local.getId()) {
			field.addChip(local.chip, x, y);
			state = GameState.GAME_WAIT;
		} else if (moveId == enemy.getId()) {
			field.addChip(enemy.chip, x, y);
			if (!field.checkWin(enemy.chip)) state = GameState.GAME_TURN;
			else state = GameState.GAME_WAIT;
		} else if (moveId != local.getId() && moveId != enemy.getId()) {
			System.err.println("UNKNOWN PLAYER DETECTED");
			state = GameState.UNCONNECTED;
		}
	}

	/**
	 * Returns the view object of the client
	 * @return view object of the client
	 */
	/* Pure */public View getView() {
		return view;
	}

	/**
	 * Closes the used <code>Protocoller</code> and terminates the client.
	 */
	public void shutdown() {
		if (state != GameState.UNCONNECTED) protocoller.close();
		state = GameState.SHUTDOWN;
	}
	
	/**
	 * Returns the <code>Protocoller</code> of the client.
	 * @return the <code>Protocoller</code> object of the client.
	 */
	/* Pure */public Protocoller getProtocoller() {
		return protocoller;
	}
	
	/*@ pure */public boolean inGame() {
		return state == GameState.GAME_TURN || state == GameState.GAME_WAIT || state == GameState.GAME_AWAITING_RESPONSE;
	}

	public Player getLocalPlayer() {
		return local;
	}

	public void setLocalPlayer(Player local) {
		this.local = local;
	}

	
	private static final double YUNO_PRUDENCE = 0.5D;
	
	public static void main(String[] args) {
		args = new String[]{"AllesKaas", "-h"};
		if (args.length != 2) {
			System.out.println("Specify username and type of player");
		} else {
			String username = args[0];
			Player localPlayer;
			if (args[1].toLowerCase().equals("-h")) {
				localPlayer = new HumanPlayer(username, Chip.RED);
			} else if (args[1].toLowerCase().equals("-n")) {
				localPlayer = new NaiveAI(username, Chip.RED);
			} else if (args[1].toLowerCase().equals("-s")) {
				localPlayer = new Yuno(username, Chip.RED, YUNO_PRUDENCE);
			} else {
				System.out.println("Usage: [username] [-h (=Human) | -n (=Naive AI) | -s (=Smart AI)]");
				return;
			}
			Client c = new Client(localPlayer);
			c.runtimeLoop();
		}
	}
}
