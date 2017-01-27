package client.ui;

import java.util.Observer;

import client.Client;

public abstract class View implements Observer {

	protected final Client client;
	protected Controller control;
	
	public View(Client client) {
		this.client = client;
	}
	
	public void setController(Controller control) {
		this.control = control;;
	}
	
	abstract public void userInput(String input);

	abstract public void internalMessage(String msg);
	
	abstract public void chatMessage(String msg);
}
