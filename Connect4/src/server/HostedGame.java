package server;

import static client.Protocoller.*;

import java.util.concurrent.locks.ReentrantLock;

import game.BoundedField;
import game.Chip;
import game.Field;

public class HostedGame {

	/**
	 * Player participating in this game.
	 */
	private final NetworkPlayer p1, p2;
	
	/**
	 * Reference to either player 1 or player 2, depending on who has the turn.
	 */
	private NetworkPlayer playerWithTurn;
	
	/**
	 * The field on which the game is played.
	 */
	private final Field field;
	
	/**
	 * Create a new game and inform the participants.
	 * @param server the server on which this game is hosted.
	 * @param player1 Player 1 participating in this game.
	 * @param player2 Player 2 participating in this game
	 * @param dimX the x-dimension of the field used in this game.
	 * @param dimY the y-dimension of the field used in this game.
	 * @param dimZ the z-dimension of the field used in this game.
	 * @param winLength the number of chips in a row needed to win this game.
	 */
	public HostedGame(Server server, NetworkPlayer player1, NetworkPlayer player2, int dimX, int dimY, int dimZ, int winLength) {
		//Initialize the participating players
		p1 = player1;
		p2 = player2;
		p1.chip = Chip.RED;
		p2.chip = Chip.YELLOW;
		
		//Set the game reference in player
		p1.enroll(this);
		p2.enroll(this);
		
		//Decide randomly who has the first turn
		playerWithTurn = (Math.random() < 0.5D) ? p1 : p2;
		
		//Inform the clients that a game has started
		p1.cmdGame(p2.username, p2.id, dimX, dimY, dimZ, playerWithTurn.id, winLength);
		p2.cmdGame(p1.username, p1.id, dimX, dimY, dimZ, playerWithTurn.id, winLength);
		
		//Create the playing field
		field = new BoundedField(dimX, dimY, dimZ, winLength);
		
		System.out.println("New game between" + p1.toString() + " and " + p2.toString());
	}
	
	public NetworkPlayer getOpponent(NetworkPlayer inquirer) {
		return (p1.equals(inquirer)) ? p2 : p1;
	}

	private final ReentrantLock lock = new ReentrantLock();
	synchronized public void moveReceived(NetworkPlayer player, int x, int y) {
		lock.lock();
		try {
			if (field.inBounds(x, y) && !field.columnFull(x, y)) {
				field.addChip(player.chip, x, y);
				if (field.checkWin(player.chip)) {
					p1.cmdGameEnd(player.id);
					p2.cmdGameEnd(player.id);
					endGame();
				} else if (field.checkFull()) {
					p1.cmdGameEnd(-1);
					p2.cmdGameEnd(-1);
					endGame();
				} else {
					playerWithTurn = getOpponent(player);
					p1.cmdMoveSuccess(x, y, player.id, playerWithTurn.id);
					p2.cmdMoveSuccess(x, y, player.id, playerWithTurn.id);
				}
			} else {
				player.cmdReportIllegal(String.join(COMMAND_DELIMITER, SERVER_ILLEGAL, CLIENT_MOVE, String.valueOf(x), String.valueOf(y)));
				player.newTransgression();
			}
		} finally {
			lock.unlock();
		}
	}

	private void endGame() {
		if (p1.state == PlayerState.IN_GAME) p1.state = PlayerState.IDLE;
		if (p2.state == PlayerState.IN_GAME) p2.state = PlayerState.IDLE;
		System.out.println("Game ended between " + p1.toString() + " and " + p2.toString());
	}

	public void playerBanned(NetworkPlayer player, String reason) {
		NetworkPlayer other = getOpponent(player);
		other.cmdPlayerLeft(player.id, reason);
	}
}
