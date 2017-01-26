package client.protocol;

public interface ScoreboardCapabilityClient {

	/**
	 * Send this command to the server to have the server return all the scoreboard entries one for one via the server-side SENDSCOREBOARDENTRY command
	 */
	public void cmdGetScoreboard();
}
