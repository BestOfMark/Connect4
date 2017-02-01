package client.player;

import java.awt.Point;

import game.Chip;
import game.Field;

public abstract class ComputerPlayer extends Player {

	private static final String PREFIX = "[AI]";
	
	/**
	 * Calls the constructor of Player
	 * @param username specifies the username of the ComputerPlayer
	 * @param chip specifies the chip used by the ComputerPlayer
	 */
	//@ requires chip != null;
	public ComputerPlayer(String username, Chip chip) {
		super(PREFIX + username, chip);
	}

	/**
	 * Starts the thinking process of the <code>ComputerPlayer</code> and returns the move the AI has determined on.
	 * @param fieldCopy is a copy of the current playing field used by the ComputerPlayer to determine
	 * the next move.
	 * @return the move in the form of a java.awt.Point
	 */
	//@ requires fieldCopy != null;
	abstract public Point getMove(Field fieldCopy);

}
