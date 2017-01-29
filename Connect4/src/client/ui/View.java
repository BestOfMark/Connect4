package client.ui;

import java.util.Observer;

import client.Client;

public abstract class View implements Observer {

	protected final Client client;
	protected Controller control;
	
	/**
	 * Sets the client of View to the specified client
	 * @param client the client object used to call this constructor
	 */
	//@ requires client != null;
	public View(Client client) {
		this.client = client;
	}
	/**
	 * Sets the controller of this View
	 * @param control the specified controller object used to call this method
	 */
	//@requires control != null;
	public void setController(Controller control) {
		this.control = control;;
	}
	
	/**
	 * Prints the user input on the UI
	 * @param input the input that was entered by the user
	 */
	abstract public void userInput(String input);

	/**
	 * Prints the message from the client
	 * @param msg the message that was sent by the client
	 */
	abstract public void internalMessage(String msg);
	/**
	 * Prints the chat message received from the server
	 * @param msg the message that was sent by a the server
	 */
	abstract public void chatMessage(String msg);
}
