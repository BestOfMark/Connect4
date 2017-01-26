package core.protocol;

public interface ChatCapabilityClient {

	/**
	 * Send a chat message to the server, which in his turn will broadcast it to (all) capable clients
	 * @param msg the message to be sent
	 * @param recipientID the server-generated id to whom the message should be sent to. To send to
	 * everyone use -1.
	 */
	public void cmdChat(int recipientID, String msg);
}
