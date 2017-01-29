package client;

public class MalFormedServerAddressException extends Exception {
	private static final long serialVersionUID = 1L;
	
	private final String faultyAddress;
	
	/**
	 * An exception thrown when the given address could not be parsed.
	 */
	public MalFormedServerAddressException(String faultyAddress) {
		this.faultyAddress = faultyAddress;
	}

	@Override
	public String getMessage() {
		return "The given address cannot be correctly parsed: " + faultyAddress;
	}
	
}
