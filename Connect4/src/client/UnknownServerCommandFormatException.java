package client;

public class UnknownServerCommandFormatException extends Exception {
	private static final long serialVersionUID = 1L;
	
	private final String cmd;
	private final String fullCmd;
	
	public UnknownServerCommandFormatException(String cmd, String fullCmd) {
		this.cmd = cmd;
		this.fullCmd = fullCmd;
	}
	
	@Override
	public String getMessage() {
		return "Not recognized format of " + cmd + " server command: " + fullCmd;
	}
}
