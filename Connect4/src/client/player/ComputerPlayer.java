package client.player;

import game.Chip;
import game.Field;

public abstract class ComputerPlayer extends Player {

	/**
	 * Calls the constructor of Player
	 * @param username specifies the username of the ComputerPlayer
	 * @param chip specifies the chip used by the ComputerPlayer
	 */
	//@ requires chip != null;
	public ComputerPlayer(String username, Chip chip) {
		super(username, chip);
	}

	/**
	 * Starts the thinking process of the ComputerPlayer
	 * @param fieldCopy is a copy of the current playing field used by the ComputerPlayer to determine
	 * the next move.
	 */
	//@ requires fieldCopy != null;
	abstract public void startThinking(Field fieldCopy);

}
