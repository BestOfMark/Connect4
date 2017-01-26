package core.protocol;

public interface ScoreboardCapabilityServer {

	/**
	 * Send one scoreboard entry to a client that invoked the GETSCOREBOARD command
	 * @param id the id of the player to which this entry belongs
	 * @param name the chosen username of the player
	 * @param score the amount of times this player has won
	 */
	public void cmdSendScoreboardEntry(int id, String name, int score);
	
	/**
	 * Let the client know that all scoreboard entries have been sent.
	 */
	public void cmdEndOfScoreboardTransmission();
}
