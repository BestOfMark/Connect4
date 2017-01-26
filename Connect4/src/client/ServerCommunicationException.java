package client;

public class ServerCommunicationException extends Exception {
	private static final long serialVersionUID = 1L;
	
	private final String msg;
	
	public ServerCommunicationException(String msg) {
		this.msg = msg;
	}
	
	@Override
	public String getMessage() {
		return msg;
	}
}
