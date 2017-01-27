package client.ui;

import java.util.Observer;

public abstract class View implements Observer {

	protected Controller control;
	
	public View(Controller control) {
		this.control = control;
	}
	
	abstract public void userInput(String input);

	abstract public void internalMessage(String msg);
	
	abstract public void chatMessage(String msg);
}
