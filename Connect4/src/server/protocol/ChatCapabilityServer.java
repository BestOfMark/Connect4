package server.protocol;

public interface ChatCapabilityServer {
	
	/**
	 * Sends an user-message to all capable clients, also to the client the MESSAGE command came 
	 * from.
	 * @param senderId the id of the user who sent the message
	 * @param msg the message to broadcast
	 */
	public void cmdBroadcastMessage(int senderId, String msg);

}
