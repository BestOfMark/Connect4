package client.ui;

import java.awt.Point;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

import client.player.Player;
import game.Field;

public abstract class Controller {

	protected final Player player;
	protected View view;
	
	protected static final int TIMEOUT = 60000;
	protected Point move;
	protected String address;
	protected String playerID;
	protected ReentrantLock inputWaiterLock = new ReentrantLock();
	protected Condition addressEntered = inputWaiterLock.newCondition();
	protected Condition moveGiven = inputWaiterLock.newCondition();
	protected Condition playerIDEntered = inputWaiterLock.newCondition();
	
	public Controller(Player player) {
		this.player = player;
		player.setController(this);
	}
	
	public abstract Point requestMove(Field f);
	
	public abstract String requestAddress();
	
	public abstract String requestPlayerID();

	public void setMove(Point move) {
		this.move = move;
		moveGiven.signal();
	}

	protected void setView(View v) {
		this.view = v;
	}
	
	public View getView() {
		return view;
	}
	
	public abstract void close();

}
