package client.ui;

import java.awt.Point;

import client.Client;
import client.player.Player;
import game.Field;

public abstract class Controller {

	protected Player player;
	protected View view;
	protected final Client client;
	
	protected int timeout;
	
	/**
	 * convenience constructor for subclasses of type Controller. 
	 * Sets the client and the player of this controller.
	 * @param client specifies the client linked to this controller.
	 * @param player specifies the player linked to this controller.
	 */
	//@ requires client != 0; player !=0; 
	public Controller(Client client) {
		this.client = client;
	}
	
	/**
	 * Asks the player to make a move.  
	 * @param f Field given to the player to make the move on.
	 * @return A point (x,y).
	 */
	//@ requires f != null;
	public abstract Point requestMove(Field f);
	
	/**
	 * requests the address and the port of the server to which the player wants to connect.
	 * @return the address and port entered by the player or <code>null</code> 
	 * if interrupted while waiting for input of the player.
	 */
	public abstract String requestAddress();
	
	/**
	 * Sets the view utilized by this player.
	 * @param v the specified view the will be used by the player.
	 */
	//@ requires v != null;
	public void setView(View v) {
		this.view = v;
	}
	
	/**
	 * Sets the amount of time the player has to think about a move to the 
	 * specified amount of time given by the server. 
	 * @param millis The amount of time the player has to think over a move.
	 */
	//@ requires millis > 0;
	public void setTimeout(int millis) {
		timeout = millis;
	}
	/**
	 * Closes all processes in the controller.
	 */
	public abstract void close();

	public Player getPlayer() {
		return player;
	}

	public void setPlayer(Player player) {
		this.player = player;
		client.setLocalPlayer(player);
		player.setController(this);
	}

}
