package ui;

import java.awt.Point;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.concurrent.TimeUnit;

import game.Field;
import player.ComputerPlayer;
import player.Player;

public class TUIController extends Controller {
	
	private TUI tui;
	
	public TUIController(Player player) {
		super(player);
		tui = new TUI(this);
		setView(tui);
		spawnInputHandler();
	}
	
	private void spawnInputHandler() {
		InputHandler ih = new InputHandler();
		ih.start();
	}

	@Override
	public Point requestMove(Field f) {
		view.internalMessage("What is your move?");
		inputWaiterLock.lock();
		try {
			if (player instanceof ComputerPlayer) {
				((ComputerPlayer) player).startThinking(f);
			}
			try {
				moveGiven.await(60, TimeUnit.SECONDS);
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
				addressEntered.await(10, TimeUnit.SECONDS);
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
	
	private class InputHandler extends Thread {
		
		@Override
		public void run() {
			try {
				BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
				String input;
				while ((input = br.readLine()) != null) {
					view.userInput(input);
					parse(input);
				}
			} catch (IOException e) {
				System.err.println("Problem with the inputhandler:");
				System.err.println(e.getMessage());
				System.err.println("Resetting inputhandler:");
				spawnInputHandler();
			}
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
				} else {
					System.out.println("Unknown command");
				}
			} finally {
				inputWaiterLock.unlock();
			}
		} else {
			//Chat
		}
	}
	
	private static final String CMD_ADDRESS = "address";
	private static final String CMD_MOVE = "move";
}
