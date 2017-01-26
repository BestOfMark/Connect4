package client.player;

import java.awt.Point;
import java.util.Random;

import game.Chip;
import game.Field;

public class LookingForBetterName extends ComputerPlayer {

	private static final String NAME = "LookingForBetterName";
	
	public LookingForBetterName(Chip chip) {
		super(NAME, chip);
	}

	@Override
	public void startThinking(Field fieldCopy) {
		Random rand = new Random();
		int x = -1, y = -1;
		do {
			x = rand.nextInt(fieldCopy.dimX);
			y = rand.nextInt(fieldCopy.dimY);
		} while (!fieldCopy.inBounds(x, y));
		control.setMove(new Point(x,y));
	}

}
