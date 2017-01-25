package player;

import game.Chip;
import ui.Controller;

public abstract class Player {

	public final String username;
	public final Chip chip;
	protected Controller control;
	
	public Player(String username, Chip chip) {
		this.username = username;
		this.chip = chip;
	}

	public void setController(Controller c) {
		control = c;
	}
}
