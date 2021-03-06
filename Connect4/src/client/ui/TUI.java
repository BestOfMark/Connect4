package client.ui;

import java.util.Observable;
import java.util.concurrent.locks.ReentrantLock;

import client.Client;

public class TUI extends View {

	private final ReentrantLock consoleWriteLock = new ReentrantLock();
	
	/**
	 * calls the Constructor of View.
	 * @param client specifies the client used to call this constructor.
	 */
	//@ requires client != null;
	public TUI(Client client) {
		super(client);
	}

	@Override
	public void update(Observable o, Object arg) {
		System.out.println(o);
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
