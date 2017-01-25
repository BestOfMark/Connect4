package ui;

import java.awt.Point;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

import game.Field;
import player.Player;

public abstract class Controller {

	protected final Player player;
	protected View view;
	
	protected static final int TIMEOUT = 60000;
	protected Point move;
	protected String address;
	
	protected ReentrantLock inputWaiterLock = new ReentrantLock();
	protected Condition addressEntered = inputWaiterLock.newCondition();
	protected Condition moveGiven = inputWaiterLock.newCondition();
	
	public Controller(Player player) {
		this.player = player;
		player.setController(this);
	}
	
	public abstract Point requestMove(Field f);
	
	public abstract String requestAddress();

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

}
