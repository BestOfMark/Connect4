package server;

import static client.Protocoller.*;

import java.util.concurrent.locks.ReentrantLock;

import game.BoundedField;
import game.Chip;
import game.Field;

public class HostedGame {

	private final NetworkPlayer p1, p2;
	private NetworkPlayer playerWithTurn;
	private Field field;
	
	private static final int DIM_X = 4, DIM_Y = 4, DIM_Z = 4, WIN = 4;
	
	public HostedGame(Server server, NetworkPlayer player1, NetworkPlayer player2) {
		p1 = player1;
		p2 = player2;
		p1.chip = Chip.RED;
		p2.chip = Chip.YELLOW;
		p1.enroll(this);
		p2.enroll(this);
		playerWithTurn = (Math.random() < 0.5D) ? p1 : p2;
		p1.cmdGame(p2.username, p2.id, DIM_X, DIM_Y, DIM_Z, playerWithTurn.id, WIN);
		p2.cmdGame(p1.username, p1.id, DIM_X, DIM_Y, DIM_Z, playerWithTurn.id, WIN);
		
		field = new BoundedField(DIM_X, DIM_Y, DIM_Z, WIN);
		
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
