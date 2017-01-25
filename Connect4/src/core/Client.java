package core;

import java.awt.Point;

import game.BoundedField;
import game.Chip;
import game.Field;
import player.HumanPlayer;
import player.Player;
import ui.Controller;
import ui.TUIController;
import ui.View;

public class Client {

	private Controller control;
	private Field field;
	public static boolean exitRequested = false;
	private View view;
	
	private enum GameState {
		UNCONNECTED, IDLE, GAME_TURN, GAME_WAIT;
	}
	
	private GameState state = GameState.UNCONNECTED;
	
	public Client() {
		Player p = new HumanPlayer("testUser", Chip.RED);
		control = new TUIController(p);
		view = control.getView();
	}

	private void runtimeLoop() {
		while (!exitRequested) {
			switch (state) {
			case UNCONNECTED:
				String address = control.requestAddress();
				if (address != null) {
					view.internalMessage("Obtained address " + address);
					state = GameState.IDLE;
				}
				break;
			case IDLE:
				field = new BoundedField(4, 4, 4, 4);
				state = GameState.GAME_TURN;
				break;
			case GAME_TURN:
				Point p = control.requestMove(field.deepCopy());
				if (p != null) {
					view.internalMessage("Obtained move " + p.toString());
				}
				break;
			case GAME_WAIT:
				break;
			}
		}
	}

	protected void welcomed() {
		
	}

	public static void main(String[] args) {
		Client c = new Client();
		c.runtimeLoop();
	}

}
