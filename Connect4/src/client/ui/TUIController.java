package client.ui;

import java.awt.Point;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

import client.Client;
import client.player.ComputerPlayer;
import client.player.Player;
import game.Field;

public class TUIController extends Controller {
	
	private TUI tui;
	private InputHandler ih;
	
	private static ReentrantLock inputWaiterLock = new ReentrantLock();
	private static Condition addressEntered = inputWaiterLock.newCondition();
	private static Condition moveGiven = inputWaiterLock.newCondition();
	private static Condition playerIDEntered = inputWaiterLock.newCondition();
	
	private Point move;
	private String address;
	private String playerID;
	
	private static final int MESSAGE_FREQUENCY = 30;
	
	public TUIController(Client client, Player player) {
		super(client, player);
		spawnInputHandler();
	}
	
	private void spawnInputHandler() {
		ih = new InputHandler();
		ih.start();
	}

	@Override
	public Point requestMove(Field f) {
		view.internalMessage("What is your move?");
		inputWaiterLock.lock();
		try {
			if (player instanceof ComputerPlayer) {
				new Thread(new Runnable() {
					public void run() {
						//Wait a bit such that the move is set in this thread after the await() is called in the outer thread
						try {
							Thread.sleep(2);
						} catch (InterruptedException e) {
							//Oh shit
						}
						((ComputerPlayer) player).startThinking(f);
					};
				}).start();
			}
			try {
				moveGiven.await(timeout, TimeUnit.MILLISECONDS);
				return move;
			} catch (InterruptedException e) {
				System.err.println("Interrupted while waiting for player to input move.");
				System.err.println(e.getMessage());
				System.err.println("Returning null");
			}
			return null;
		} finally {
			inputWaiterLock.unlock();
		}
	}

	@Override
	public String requestAddress() {
		inputWaiterLock.lock();
		try {
			view.internalMessage("Please input the ip-address of the server");
			try {
				addressEntered.await(MESSAGE_FREQUENCY, TimeUnit.SECONDS);
				return address;
			} catch (InterruptedException e) {
				System.err.println("Interrupted while waiting for player to input server address.");
				System.err.println(e.getMessage());
				System.err.println("Returning null");
			}
			return null;
		} finally {
			inputWaiterLock.unlock();
		}
	}
	
	@Override
	synchronized public void setMove(Point move) {
		inputWaiterLock.lock();
		try {
			this.move = move;
			moveGiven.signal();
		} finally {
			inputWaiterLock.unlock();
		}
	}
	
	@Override
	public String requestPlayerID() {
		 view.internalMessage("Please input the ip-address of the desired opponent");
		 try {
			 playerIDEntered.await(MESSAGE_FREQUENCY, TimeUnit.SECONDS);
			 return playerID;
		 } catch(InterruptedException e) {
			System.err.println("Interrupted while waiting for player to input server address.");
			System.err.println(e.getMessage());
			System.err.println("Returning null");
		 }
		return null;
	}
	
	@Override
	public void close() {
		ih.isCloseRequested = true;
	}
	
	private class InputHandler extends Thread {
		
		private boolean isCloseRequested = false;
		
		@Override
		public void run() {
			try {
				BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
				String input;
				while (!isCloseRequested && (input = br.readLine()) != null) {
					view.userInput(input);
					parse(input);
				}
			} catch (IOException e) {
				System.err.println("Problem with the inputhandler:");
				System.err.println(e.getMessage());
				System.err.println("Resetting inputhandler:");
				spawnInputHandler();
			}
			System.out.println("Exiting local input handler");
		}
	}
	
	private void parse(String input) {
		if (input.startsWith("\\")) {
			input = input.substring(1).toLowerCase();
			inputWaiterLock.lock();
			try {
				if (input.startsWith(CMD_ADDRESS)) {
					this.address = input.substring(CMD_ADDRESS.length()).trim();
					addressEntered.signal();				
				} else if (input.startsWith(CMD_MOVE)) {
					String[] args = input.substring(CMD_MOVE.length()).replaceAll("\\D", " ").trim().split("\\s+");
					if (args.length != 2) {
						view.internalMessage("Wrong argument(s)");
						view.internalMessage("Usage: \\move x(int) y(int)");
					} else {
						int x = Integer.parseInt(args[0]);
						int y = Integer.parseInt(args[1]);
						move = new Point(x,y);
						moveGiven.signal();
					}
				} else if (input.startsWith(CMD_CHAT)) {
					view.internalMessage("Yet to implement");
				} else if (input.startsWith(CMD_INVITE)) {
					view.internalMessage("Yet to implement");
				} else if (input.startsWith(CMD_GETSCOREBOARD)) {
					view.internalMessage("Yet to implement");
				} else if (input.equals(CMD_EXIT)) {
					close();
				} else {
					System.out.println("Unknown command");
				}
			} finally {
				inputWaiterLock.unlock();
			}
		}
	}
	
	private static final String CMD_ADDRESS = "address";
	private static final String CMD_MOVE = "move";
	private static final String CMD_EXIT = "exit";
	private static final String CMD_CHAT = "chat";
	private static final String CMD_INVITE = "invite";
	private static final String CMD_GETSCOREBOARD = "scoreboard";
}
