package client;

import java.awt.Point;
import java.io.IOException;

import client.player.ComputerPlayer;
import client.player.HumanPlayer;
import client.player.Player;
import client.ui.Controller;
import client.ui.TUIController;
import client.ui.View;
import game.BoundedField;
import game.Chip;
import game.Field;

public class Client {

	private Controller control;
	private Field field;
	private boolean exitRequested = false;
	private View view;
	private static final int MAGIC_NUMBER = 00; 
	private Player local, enemy;
	private Protocoller protocoller;
	
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
				} else {
					view.internalMessage("Turn timed out");
					
					break;
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
		control.setTimeout(millis);
		local.setId(userID);
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
	
	public void chatReceived(int sendId, String msg) {
		if (sendId == enemy.getId()) {
			view.chatMessage(enemy.username + ": " + msg);
		} else {
			view.chatMessage(sendId + ": " + msg);
		}
	}

	public void illegalCommand(String input) {
		view.internalMessage(input);
		if (input.contains(Protocoller.CLIENT_MOVE)) {
			if (local instanceof ComputerPlayer) state = GameState.UNCONNECTED;
		}
	}

	public void opponentLeft(int enemyID, String string) {
		view.internalMessage(string);
		state = GameState.IDLE;
	}

	public void gameOver(int id) {
		if (id == local.getId()) {
			view.internalMessage("You have won the game");
		} else if (id == enemy.getId()) {
			view.internalMessage("You have lost the game");
		} else if (id == -1) {
			view.internalMessage("The game has ended in a tie");
		} else {
			view.internalMessage("Weird ID received");			
		}
		state = GameState.CONNECTED;
	}

	public void receivedMove(int x, int y, int moveId, int nextId) {
		if (moveId == local.getId()) {
			field.addChip(local.chip, x, y);
			state = GameState.GAME_WAIT;
		} else if (moveId == enemy.getId()) {
			field.addChip(enemy.chip, x, y);
			state = GameState.GAME_TURN;
		} else if (moveId != local.getId() && moveId != enemy.getId()) {
			state = GameState.UNCONNECTED;
		}
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
	
	public void exit() {
		
	}

	public static void main(String[] args) {
		Client c = new Client();
		c.runtimeLoop();
	}



}
