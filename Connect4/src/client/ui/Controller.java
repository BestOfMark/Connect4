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
	
	public Controller(Client client, Player player) {
		this.client = client;
		this.player = player;
		player.setController(this);
	}
	
	public abstract Point requestMove(Field f);
	
	public abstract String requestAddress();
	
	public abstract String requestPlayerID();

	public abstract void setMove(Point p);

	public void setView(View v) {
		this.view = v;
	}
	
	public void setTimeout(int millis) {
		timeout = millis;
	}
	
	public abstract void close();

}
