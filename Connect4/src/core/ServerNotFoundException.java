package core;

public class ServerNotFoundException extends Exception {

	private final String address;
	private final int port;
	
	public ServerNotFoundException(String address, int port) {
		this.address = address;
		this.port = port;
	}

	@Override
	public String getMessage() {
		return "The server at " + address + " (port = " + port + ") could not be found"; 
	}
}
