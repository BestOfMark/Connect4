package client;

public class ServerNotFoundException extends Exception {
	private static final long serialVersionUID = 1L;
	
	private final String address;
	private final int port;
	
	/**
	 * An exception thrown when the specified IP-address and/or port could not be found.
	 */
	public ServerNotFoundException(String address, int port) {
		this.address = address;
		this.port = port;
	}

	@Override
	public String getMessage() {
		return "The server at " + address + " (port = " + port + ") could not be found"; 
	}
}
