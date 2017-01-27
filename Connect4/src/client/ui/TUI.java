package client.ui;

import java.util.Observable;
import java.util.concurrent.locks.ReentrantLock;

public class TUI extends View {

	private final ReentrantLock consoleWriteLock = new ReentrantLock();
	
	public TUI(Controller control) {
		super(control);
	}

	@Override
	public void update(Observable o, Object arg) {
		// TODO Auto-generated method stub

	}

	@Override
	public void userInput(String input) {
		consoleWriteLock.lock();
		try {
			System.out.println("INPUT: " + input);
		} finally {
			consoleWriteLock.unlock();
		}
	}

	@Override
	public void internalMessage(String msg) {
		consoleWriteLock.lock();
		try {
			System.out.println("CLIENT: " + msg);
		} finally {
			consoleWriteLock.unlock();
		}
	}

	@Override
	public void chatMessage(String msg) {
		consoleWriteLock.lock();
		try {
			System.out.println("CHAT: " + msg);
		} finally {
			consoleWriteLock.unlock();
		}
	}

}
