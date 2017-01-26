package client.player;

import client.ui.Controller;
import game.Chip;

public abstract class Player {

	public final String username;
	public final Chip chip;
	private int id;
	protected Controller control;
	
	public Player(String username, Chip chip) {
		this.username = username;
		this.chip = chip;
	}

	public void setController(Controller c) {
		control = c;
	}

	public int getId() {
		return id;
	}

	public void setId(int id) {
		this.id = id;
	}
}
