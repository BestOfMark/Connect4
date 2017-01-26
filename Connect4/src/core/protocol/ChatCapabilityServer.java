package core.protocol;

public interface ChatCapabilityServer {
	
	/**
	 * Sends an user-message to all capable clients, also to the client the MESSAGE command came from.
	 * @param msg the message to broadcast
	 */
	public void cmdBroadcastMessage(String msg);

}
