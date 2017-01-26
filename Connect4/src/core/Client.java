package core;

import java.awt.Point;
import java.io.IOException;

import game.BoundedField;
import game.Chip;
import game.Field;
import player.ComputerPlayer;
import player.HumanPlayer;
import player.LookingForBetterName;
import player.Player;
import ui.Controller;
import ui.TUIController;
import ui.View;

public class Client {

	private Controller control;
	private Field field;
	private boolean exitRequested = false;
	private View view;
	private int millis, serverMagicNumber;
	private static final int MAGIC_NUMBER = 00; 
	private Player local, enemy, dumbAi;
	private Protocoller protocoller;
	
	private enum GameState {
		UNCONNECTED, IDLE, GAME_TURN, GAME_WAIT, CONNECTED;
	}
	
	private GameState state = GameState.UNCONNECTED;
	
	public Client() {
		local = new HumanPlayer("testUser", Chip.RED);
		control = new TUIController(local);
		view = control.getView();
		dumbAi = new LookingForBetterName(local.chip);
	}

	private void runtimeLoop() {
		while (!exitRequested) {
			switch (state) {
			case UNCONNECTED:
				String address = control.requestAddress();
				if (address != null) {
					view.internalMessage("Obtained address " + address);
					try {
						protocoller = new Protocoller(this, address);
						try {
							protocoller.cmdHello(local.username, local instanceof ComputerPlayer, MAGIC_NUMBER);
							state = GameState.IDLE;
						} catch (IOException e) {
							view.internalMessage("Hello command failed");
						}
					} catch (MalFormedServerAddressException e) {
						view.internalMessage(e.getMessage());
					} catch (ServerNotFoundException e) {
						view.internalMessage(e.getMessage());
					} catch (ServerCommunicationException e) {
						view.internalMessage(e.getMessage());
					}
				}
				break;
			case IDLE:
				break;
			case CONNECTED:
				break;
			case GAME_TURN:
				Point p = control.requestMove(field.deepCopy());
				if (p != null) {
					view.internalMessage("Obtained move " + p.toString());
				}
				if (!field.inBounds(p.x, p.y) || field.columnFull(p.x, p.y)) {
					if (local instanceof ComputerPlayer) {
						p = new Point(0,0);
					} else {
						view.internalMessage("Invalid move");
						break;
					}
				}
				try {
					protocoller.cmdMove(p.x, p.y);
				} catch (IOException e) {
					view.internalMessage("Error while sending move");
					protocoller.close();
					state = GameState.UNCONNECTED;
				}
				break;
			case GAME_WAIT:
				break;
			}
		}
	}

	protected void welcomed(int userID, int millis, int magicNumber) {
		this.millis = millis;
		local.setId(userID);
		serverMagicNumber = magicNumber;
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
		if (local instanceof HumanPlayer){state = GameState.GAME_TURN;}
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

	public void shutdown() {
		protocoller.close();
		exitRequested = true;
	}
	
	public Protocoller getProtocoller() {
		return protocoller;
	}

	public static void main(String[] args) {
		Client c = new Client();
		c.runtimeLoop();
	}



}
