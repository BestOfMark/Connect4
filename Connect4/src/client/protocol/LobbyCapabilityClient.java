package client.protocol;

public interface LobbyCapabilityClient {
	
	/**
	 * Let's the server know that you want to play against opponent with 
	 * the given server-generated id.
	 * @param desiredOpponentID the ID of the desired opponent
	 */
	public void cmdInvite(int desiredOpponentID);
}
