package client.ui;

import java.awt.Point;

import client.Client;
import client.player.ComputerPlayer;
import client.player.Player;
import game.Field;

public class GUIController extends Controller {

	private GUI gui;
	
	public GUIController(Client client) {
		super(client);
	}
	
	@Override
	public void setView(View v) {
		if (v instanceof GUI) {
			gui = (GUI) v;
		}
	}
	
	@Override
	public String requestAddress() {
		return gui.getAddress();
	}
	
	private static final String WRONG_SYNTAX = "Wrong input for move";
	
	@Override
	public Point requestMove(Field fCopy) {
		if (player instanceof ComputerPlayer) {
			return ((ComputerPlayer) player).getMove(fCopy);
		} else {
			String input = gui.getMove();
			if (input == null) return null;
			if (!input.matches("\\d+\\D+\\d+")) {
				view.internalMessage(WRONG_SYNTAX);
			} else {
				String[] args = input.split("\\D+");
				try {
					return new Point(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
				} catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
					view.internalMessage(WRONG_SYNTAX);
				}
			}
			return null;
		}
	}
	
	@Override
	public void close() {
		gui.close();
	}
}
