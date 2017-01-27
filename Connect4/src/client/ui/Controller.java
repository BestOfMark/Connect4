package client.ui;

import java.awt.Point;
import client.player.Player;
import game.Field;

public abstract class Controller {

	protected final Player player;
	protected View view;
	
	protected static final int TIMEOUT = 60000;
	
	public Controller(Player player) {
		this.player = player;
		player.setController(this);
	}
	
	public abstract Point requestMove(Field f);
	
	public abstract String requestAddress();
	
	public abstract String requestPlayerID();

	public abstract void setMove(Point p);

	protected void setView(View v) {
		this.view = v;
	}
	
	public View getView() {
		return view;
	}
	
	public abstract void close();

}
