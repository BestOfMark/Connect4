package client.player;

import client.ui.Controller;
import game.Chip;

public abstract class Player {

	//@ invariant username != null;
	public final String username;
	//@ invariant chip != null;
	public final Chip chip;
	private int id;
	protected Controller control;
	
	/**
	 * Convenience constructor for subclasses to set the user name and the chip of the player.
	 * @param username specifies the name of the player
	 * @param chip specifies the chip used by this player.
	 */
	//@ requires chip != null;
	public Player(String username, Chip chip) {
		this.username = username;
		this.chip = chip;
	}
	
	/**
	 * Sets the controller for this player.
	 * @param c specifies the controller of the player
	 */
	//@ ensures \control == c;
	public void setController(Controller c) {
		control = c;
	}

	/**
	 * returns the id of the player.
	 * @return the integer value of the id of the player
	 */
	/*@ pure */public int getId() {
		return id;
	}
	
	/**
	 * Sets the id of the player.
	 * @param id the integer value of the id of the player
	 */
	//@ ensures \getID() == id;
	public void setId(int id) {
		this.id = id;
	}
}
