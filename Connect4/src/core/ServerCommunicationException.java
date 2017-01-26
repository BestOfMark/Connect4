package core;

public class ServerCommunicationException extends Exception {
	
	private final String msg;
	
	public ServerCommunicationException(String msg) {
		this.msg = msg;
	}
	
	@Override
	public String getMessage() {
		return msg;
	}
}
