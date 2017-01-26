package client.player;

import game.Chip;
import game.Field;

public abstract class ComputerPlayer extends Player {

	public ComputerPlayer(String username, Chip chip) {
		super(username, chip);
	}

	abstract public void startThinking(Field fieldCopy);

}
