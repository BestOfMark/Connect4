package core;

import java.awt.Point;
import java.io.IOException;

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
	private int millis, magicnumber;
	private static final int MAGIC_NUMBER = 00; 
	private Player local, enemy;
	
	
	private enum GameState {
		UNCONNECTED, IDLE, GAME_TURN, GAME_WAIT, CONNECTED;
	}
	
	private GameState state = GameState.UNCONNECTED;
	
	public Client() {
		local = new HumanPlayer("testUser", Chip.RED);
		control = new TUIController(local);
		view = control.getView();
	}

	private void runtimeLoop() {
		while (!exitRequested) {
			switch (state) {
			case UNCONNECTED:
				String address = control.requestAddress();
				if (address != null) {
					view.internalMessage("Obtained address " + address);
					try {
						Protocoller protocoller = new Protocoller(this, address);
						protocoller.cmdHello(local.username, local instanceof player.ComputerPlayer, MAGIC_NUMBER);
					} catch (MalFormedServerAddressException e) {
						view.internalMessage(e.getMessage());
						e.printStackTrace();
					} catch (ServerNotFoundException e) {
						view.internalMessage(e.getMessage());
						e.printStackTrace();
					} catch (ServerCommunicationException e) {
						view.internalMessage(e.getMessage());
						e.printStackTrace();
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}
				break;
			case CONNECTED:
				
				break;
			case IDLE:
				break;
			case GAME_TURN:
				Point p = control.requestMove(field.deepCopy());
				if (p != null) {
					view.internalMessage("Obtained move " + p.toString());
				}
				state = GameState.GAME_WAIT;
				break;
			case GAME_WAIT:
				break;
			}
		}
	}

	protected void welcomed(int userID, int millis, int magicNumber) {
		this.millis = millis;
		state = GameState.CONNECTED;
	}
	
	protected void newGame(String enemyName, int enemyID, int boardSizeX, int boardSizeY, int boardSizeZ, int startingPlayer, int winLength) {
		enemy = new HumanPlayer(enemyName, local.chip.other());
		field = new BoundedField(boardSizeX, boardSizeY, boardSizeZ, winLength);
		if (startingPlayer == enemyID) {
			state = GameState.GAME_WAIT;
		} else {
			state = GameState.GAME_TURN; 			
		}
	}
	
	public void chatReceived(int parseInt, String string) {
		// TODO Auto-generated method stub
		
	}

	public void illegalMove(String input) {
		view.internalMessage(input);
		if (local instanceof player.HumanPlayer){state = GameState.GAME_TURN;}
		else {
			state = GameState.UNCONNECTED;
		}
	}

	public void opponentLeft(int enemyID, String string) {
		view.internalMessage(string);
		state = GameState.IDLE;
	}

	public void gameOver(int parseInt) {
		// TODO Auto-generated method stub
		
	}

	public void receivedMove(int parseInt, int parseInt2, int parseInt3, int parseInt4) {
		// TODO Auto-generated method stub
		
	}

	public View getView() {
		return view;
	}

	public static void main(String[] args) {
		Client c = new Client();
		c.runtimeLoop();
	}



}
