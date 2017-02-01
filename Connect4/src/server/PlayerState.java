package server;

/**
 * States the player can be in. <br>
 * <br>
 * <b><code>UNKNOWN...</code></b> - The player has just connected and no HELLO command has 
 * been received.<br>
 * <b><code>IDLE......</code></b> - The player has introduced itself with the HELLO command.<br>
 * <b><code>WAITING...</code></b> - The player has sent the REQUEST command and is waiting for a 
 * game.<br>
 * <b><code>IN_GAME...</code></b> - The player is currently in-game.<br>
 * <b><code>LEFT......</code></b> - The player disconnected.<br>
 * <b><code>ERRORED...</code></b> - The player's communication failed.<br>
 * <b><code>BANNED....</code></b> - THe player is banned because of too many requests or illegal
 * moves.<br>
 */
public enum PlayerState {
	UNKNOWN, IDLE, WAITING, IN_GAME, LEFT, ERRORED, BANNED;
}
