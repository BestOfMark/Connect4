package client;

public class ServerCommunicationException extends Exception {
	private static final long serialVersionUID = 1L;
	
	private final String msg;
	
	/**
	 * An Exception thrown when the message could not be send to the server. 
	 */
	public ServerCommunicationException(String msg) {
		this.msg = msg;
	}
	
	@Override
	public String getMessage() {
		return msg;
	}
}
