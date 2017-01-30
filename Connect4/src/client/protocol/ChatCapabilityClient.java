package client.protocol;

import java.io.IOException;

public interface ChatCapabilityClient {

	/**
	 * Send a chat message to the server, which in his turn will broadcast it to all capable clients
	 * @param msg the message to be sent
	 */
	public void cmdChat(String msg) throws IOException;
}
