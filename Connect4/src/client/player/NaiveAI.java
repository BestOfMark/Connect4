package client.player;

import java.awt.Point;
import java.util.Random;

import client.Client;
import game.Chip;
import game.Field;

public class NaiveAI extends ComputerPlayer {

	/**
	 * Calls the constructor of Player with the username LookingForBetterName
	 * @param chip specifies the chip used by the ComputerPlayer
	 */
	public NaiveAI(String username, Chip chip) {
		super(username, chip);
	}

	@Override
	public Point getMove(Field fieldCopy) {
		if (Client.DEBUG) System.out.println("AI MAKES A MOVE");
		Point instantWin = instaWin(fieldCopy);
		if (instantWin != null) return instantWin;
		Random rand = new Random();
		int x = -1, y = -1;
		do {
			x = rand.nextInt(fieldCopy.dimX);
			y = rand.nextInt(fieldCopy.dimY);
		} while (!fieldCopy.inBounds(x, y) && !fieldCopy.columnFull(x, y));
		return new Point(x,y);
	}

	public Point instaWin(Field field) {
		for (int x = 0; x < field.dimX; x++) {
			for (int y = 0; y < field.dimY; y++) {
				Field copy = field.deepCopy();
				copy.addChip(chip, x, y);
				if (copy.checkWin(chip)) return new Point(x,y);
			}
		}
		return null;
	}
}
