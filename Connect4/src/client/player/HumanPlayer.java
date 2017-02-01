package client.player;

import game.Chip;

public class HumanPlayer extends Player {

	/**
	 * Calls the constructor of player.
	 * @param username specifies the name of the player
	 * @param chip specifies the chip used by the player
	 */
	//@ requires chip != null;
	public HumanPlayer(String username, Chip chip) {
		super(username, chip);
	}

}
