package server;

import static client.Protocoller.*;

import java.util.Timer;
import java.util.TimerTask;
import java.util.concurrent.locks.Condition;
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
	 * Indicates if this game is still running or not.
	 */
	private boolean gameOver = false;
	
	/**
	 * The logic to be executed once a player's time to send a move times out is scheduled on this timer.
	 */
	private Timer timeoutTimer;
	
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
		
		//Schedule the timeout action
		scheduleTimeout(playerWithTurn);
		
		System.out.println("New game between" + p1.toString() + " and " + p2.toString());
	}
	
	/**
	 * Schedule the handling of a timeout once a the player with the current turn doesn't send his move before the timeout occurs.
	 * If a move is made in-time, this task is cancelled.
	 * @param player the player who has the turn
	 */
	private void scheduleTimeout(NetworkPlayer player) {
		System.out.println("D: Scheduling timeout for " + player.toString());
		
		//Create a new timer
		timeoutTimer = new Timer();
		
		//Schedule the timeout handling after the thinking time expires
		timeoutTimer.schedule(new TimerTask() {
			@Override
			public void run() {
				timeOut(player);
			}
		}, Server.THINK_TIME);
	}
	
	/**
	 * Find the player who is the opponent of the player passed in the argument
	 * @param inquirer the player whose opponent is returned
	 * @return the other player in this <code>HostedGame</code>
	 */
	//@ requires inquirer != null;
	//@ ensures \return != null && \return != inquirer;
	/*@ pure */ public NetworkPlayer getOpponent(NetworkPlayer inquirer) {
		return (p1.equals(inquirer)) ? p2 : p1;
	}

	/**
	 * The lock that should be acquired before a received move is handled.
	 */
	public static final ReentrantLock LOCK = new ReentrantLock();
	public static final Condition MOVES_SENT = LOCK.newCondition();
	
	/**
	 * Process a move received from one of the clients in this <code>HostedGame</code>. If the move is valid - i.e. the player who made 
	 * it has the turn <b>and</b> the chip can be added to the field - the field is updated and both connected players are notified. After
	 * every move the method checks if the player has won or if the field is full and sends the GAME_END command to the players accordingly.
	 * @param player the player from whom the command originates
	 * @param x the x-coordinate of the desired move
	 * @param y the y-coordinate of the desired move
	 */
	//@ requires player != null;
	synchronized public void moveReceived(NetworkPlayer player, int x, int y) {
		//In the case of two simultaneous commands, make sure it is executed sequentially.
		if (gameOver) return;
//		System.out.println("D: Now trying to acquire lock");
		LOCK.lock();
		try {
			//Check if the move is legal
			if (player.equals(playerWithTurn) && field.inBounds(x, y) && !field.columnFull(x, y)) {
//				System.out.println("D: Legal move");
				
				//Legal move
				field.addChip(player.chip, x, y);
				playerWithTurn = getOpponent(player);
				sendCounter = 0;
				p1.cmdMoveSuccess(x, y, player.id, playerWithTurn.id);
				p2.cmdMoveSuccess(x, y, player.id, playerWithTurn.id);
				
//				System.out.println("D: Waiting for signals");
				//Wait for the moves to be sent
				try {
					MOVES_SENT.await();
				} catch (InterruptedException e) {
					System.err.println("Awaiting moves sent got interrupted");
				}
				
//				System.out.println("D: Signals got");
				
				//Cancel the timeout and set the new timeout
				timeoutTimer.cancel();
				scheduleTimeout(playerWithTurn);
				
				//Check for game over
				if (field.checkWin(player.chip)) {
					p1.cmdGameEnd(player.id);
					p2.cmdGameEnd(player.id);
					endGame();
				} else if (field.checkFull()) {
					p1.cmdGameEnd(-1);
					p2.cmdGameEnd(-1);
					endGame();
				}
			} else {
				//Illegal move. Add a transgression
				player.cmdReportIllegal(String.join(COMMAND_DELIMITER, SERVER_ILLEGAL, CLIENT_MOVE, String.valueOf(x), String.valueOf(y)));
				player.newTransgression();
			}
		} finally {
			LOCK.unlock();
		}
	}
	
	private int sendCounter;
	
	public void incrementSendCounter() {
		if (++sendCounter == 2) {
//			System.out.println("D: Will now unlock");
			LOCK.lock();
			try {
				MOVES_SENT.signal();
			} finally {
				LOCK.unlock();
			}
		}
	}

	/**
	 * Reset the states of the players, only if they have not been banned or errored.
	 */
	private void endGame() {
		gameOver = true;
		if (p1.state == PlayerState.IN_GAME) p1.disenroll(this);
		if (p2.state == PlayerState.IN_GAME) p2.disenroll(this);
		timeoutTimer.cancel();
		System.out.println("Game ended between " + p1.toString() + " and " + p2.toString());
	}

	/**
	 * Notify the opponent when a player has been banned
	 * @param player the player who is banned
	 * @param reason the reason of the ban. This is sent to the opponent
	 */
	//@ requires player != null;
	public void playerLeft(NetworkPlayer player, String reason) {
		System.out.println("D: Endgame because player left: " + player.toString());
		NetworkPlayer other = getOpponent(player);
		other.cmdPlayerLeft(player.id, reason);
		other.cmdGameEnd(other.id);
		endGame();
	}
	
	/**
	 * Called when the current player timed out. The player that timed out is the loser and both clients are notified of the game end.
	 * @param player the player that timed out
	 */
	//@ requires player != null;
	public void timeOut(NetworkPlayer player) {
		System.out.println("D: Endgame bacause player timed out: " + player.toString());
		NetworkPlayer other = getOpponent(player);
		player.cmdGameEnd(other.id);
		other.cmdGameEnd(other.id);
		endGame();
	}
}
