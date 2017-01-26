package core.protocol;

public interface LobbyCapabilityServer {
	
	/**
	 * Send all capable clients that a new player has connected to the server
	 * @param newPlayerID the server-generated id of the new player
	 * @param newPlayerUsername the user-chosen name of the new player
	 */
	public void cmdPlayerConnect(int newPlayerID, String newPlayerUsername);
	
	/**
	 * Send all capable clients that a player disconnected from the server
	 * @param discPlayerID the server-generated id of the disconnected player
	 */
	public void cmdPlayerDisconnect(int discPlayerID);
	
	/**
	 * Send to a client that has been challenged to play against a user, that has sent the INVITE command.
	 * @param challengerID the ID of the player who sent the invite.
	 */
	public void cmdRequest(int challengerID);

}
