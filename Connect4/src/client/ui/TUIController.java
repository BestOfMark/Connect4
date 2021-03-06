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
import game.Field;

public class TUIController extends Controller {
	
	private InputHandler ih;
	
	private static ReentrantLock inputWaiterLock = new ReentrantLock();
	private static Condition addressEntered = inputWaiterLock.newCondition();
	private static Condition moveGiven = inputWaiterLock.newCondition();
	
	private Point move;
	private String address;
	
	protected static final int MESSAGE_FREQUENCY = 60;
	
	/**
	 * Calls the constructor of Controller and creates and inputHandler.
	 * @param client specifies the client of the controller
	 * @param player specifies the player of the controller
	 */
	//@ requires client != 0; player != 0;
	public TUIController(Client client) {
		super(client);
		spawnInputHandler();
	}
	/**
	 * Creates and starts a new inputHandler.
	 */
	private void spawnInputHandler() {
		ih = new InputHandler();
		ih.start();
	}

	@Override
	public Point requestMove(Field fCopy) {
		inputWaiterLock.lock();
		view.internalMessage("What is your move?");
		view.internalMessage("Format: \\move [x] [y]");
		try {
			if (player instanceof ComputerPlayer) {
				return ((ComputerPlayer) player).getMove(fCopy);
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
			view.internalMessage("Format: \\address [ip-adress] [portnumber]" );
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
	
	/**
	 * sets the next move to the point(x,y) of move.
	 * @param move a point(x,y)
	 */
	//@ requires move != null;
	synchronized public void setMove(Point move) {
		inputWaiterLock.lock();
		try {
			this.move = move;
			moveGiven.signal();
		} finally {
			inputWaiterLock.unlock();
		}
	}
	
	synchronized public void setAddress(String address) {
		inputWaiterLock.lock();
		try {
			this.address = address;
			addressEntered.signal();
		} finally {
			inputWaiterLock.unlock();
		}
	}
	
	@Override
	public void close() {
		ih.isCloseRequested = true;
		client.shutdown();
	}
	
	private class InputHandler extends Thread {
		
		private boolean isCloseRequested = false;
		
		@Override
		public void run() {
			try {
				BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
				String input;
				while (!isCloseRequested) {
					input = br.readLine();
					if (input == null) {
						break;
					}
//					view.userInput(input);
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
	
	/**
	 * This method is called when input has been received by the TUI from the player. 
	 * If the input starts with \ it will scan input for the commands address, move, 
	 * exit, chat, invite and scoreboard. After specifying the command it will take 
	 * the remainder of the string to execute the command. If the command address 
	 * is used it will retrieve the IP-address and port of the server. 
	 * If the command move is used it will retrieve the point entered and call 
	 * the move method or it will return an error if the
	 * command was used in an invalid way.
	 * if the command exit is used it will tell all processes that are going on to terminate.
	 * if the command chat is used it will send the input string to one specific user 
	 * or to all users
	 * if the command invite is used it will invite the specified user in the lobby.
	 * if the command scoreboard is used it will retrieve the scoreboard of the server. 
	 * @param inputCopy A String that was received and contains a command.
	 */
	//@ requires input != null;
	private void parse(String input) {
		String inputCopy = input;
		if (inputCopy.startsWith("\\")) {
			inputCopy = inputCopy.substring(1).toLowerCase();
			inputWaiterLock.lock();
			try {
				if (inputCopy.startsWith(CMD_ADDRESS)) {
					this.address = inputCopy.substring(CMD_ADDRESS.length()).trim();
					setAddress(address);
				} else if (inputCopy.startsWith(CMD_REQUEST)) {
					try {
						client.getProtocoller().cmdGameRequest();
					} catch (IOException e) {
						client.getView().internalMessage("Unable to request game");
					}
				} else if (inputCopy.startsWith(CMD_MOVE)) {
				
					String[] args = inputCopy.substring(CMD_MOVE.length()).replaceAll("\\D", " ")
							.trim().split("\\s+");
					if (args.length != 2) {
						view.internalMessage("Wrong argument(s)");
						view.internalMessage("Usage: \\move x(int) y(int)");
					} else {
						int x = Integer.parseInt(args[0]);
						int y = Integer.parseInt(args[1]);
						setMove(new Point(x, y));
					}
				} else if (inputCopy.startsWith(CMD_CHAT)) {
					inputCopy = inputCopy.substring(CMD_CHAT.length()).trim();
					try {
						client.getProtocoller().cmdChat(inputCopy);
					} catch (IOException e) {
						System.err.println("Error while sending CHAT");
					}
				} else if (inputCopy.startsWith(CMD_INVITE)) {
					view.internalMessage("Yet to implement");
				} else if (inputCopy.startsWith(CMD_GETSCOREBOARD)) {
					view.internalMessage("Yet to implement");
				} else if (inputCopy.equals(CMD_EXIT)) {
					System.out.println("Trying to close");
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
	private static final String CMD_REQUEST = "request";
	private static final String CMD_EXIT = "exit";
	private static final String CMD_CHAT = "chat";
	private static final String CMD_INVITE = "invite";
	private static final String CMD_GETSCOREBOARD = "scoreboard";
}
