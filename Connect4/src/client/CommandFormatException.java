package client;

public class CommandFormatException extends Exception {
	private static final long serialVersionUID = 1L;
	
	private final String cmd;
	private final String fullCmd;
	private final String source;
	
	/**
	 * An exception thrown when an entered command was not used according to the specified format.
	 */
	public CommandFormatException(String cmd, String fullCmd, String source) {
		this.cmd = cmd;
		this.fullCmd = fullCmd;
		this.source = source;
	}
	
	@Override
	public String getMessage() {
		return "Not recognized format of the " + cmd + " " + source + "-command: " + fullCmd;
	}
}
