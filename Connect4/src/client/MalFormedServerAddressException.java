package client;

public class MalFormedServerAddressException extends Exception {
	private static final long serialVersionUID = 1L;
	
	private final String faultyAddress;
	
	public MalFormedServerAddressException(String faultyAddress) {
		this.faultyAddress = faultyAddress;
	}

	@Override
	public String getMessage() {
		return "The given address cannot be correctly parsed: " + faultyAddress;
	}
	
}
