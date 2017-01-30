package client.player;

import game.Chip;
import game.Field;

public class Yuno extends ComputerPlayer {

	private double[][] potentials;
	
	public Yuno(String username, Chip chip) {
		super(username, chip);
	}

	@Override
	public void startThinking(Field field) {
		potentials = new double[field.dimX][field.dimY];
		for (int x = 0; x < field.dimX; x++) {
			for (int y = 0; y < field.dimY; y++) {
				Field fieldCopy = field.deepCopy();
				fieldCopy.addChip(chip, x, y);
				potentials[x][y] += sliceField(x, y, 1, 0).calculatePotential(true);
				potentials[x][y] += sliceField(x, y, 0, 1).calculatePotential(true);
				potentials[x][y] += sliceField(x, y, 1, 1).calculatePotential(true);
				potentials[x][y] += sliceField(x, y, 1, -1).calculatePotential(true);
			}
		}
	}

}
