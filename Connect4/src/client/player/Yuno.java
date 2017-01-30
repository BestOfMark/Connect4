package client.player;

import java.util.ArrayList;
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
				if (!field.columnFull(x, y)) {
					fieldCopy.addChip(chip, x, y);
					potentials[x][y] += totalPotential(field);
				} else {
					potentials[x][y] = 0;
				}
			}
		}
	}
	
	private double totalPotential(Field field) {
		double potential = 0;
		
		//Vertical slices
		for (int x = 0; x < field.dimX; x++) {
			potential += sliceField(field, x, 0, 0, 1).calculatePotential(chip, true);
		}
		
		//Horizontal slices
		for (int y = 0; y < field.dimY; y++) {
			potential += sliceField(field, 0, y, 1, 0).calculatePotential(chip, false);
		}
		
		//Rutger slices
		for (int x = 0; x < field.dimX; x++) {
			potential += sliceField(field, x, 0, -1, 1).calculatePotential(chip, false);
		}
		for (int y = 1; y < field.dimY; y++) {
			potential += sliceField(field, field.dimX - 1, y, -1, 1).calculatePotential(chip, false);
		}
		
		//Mark slices
		for (int x = 0; x < field.dimX; x++) {
			potential += sliceField(field, x, 0, 1, 1).calculatePotential(chip, false);
		}
		for (int y = 1; y < field.dimY; y++) {
			potential += sliceField(field, 0, y, 1, 1).calculatePotential(chip, false);
		}
		
		return potential;
	}

	private FieldSlice sliceField(Field field, int startX, int startY, int dx, int dy) {
		ArrayList<Chip[]> columns = new ArrayList<>();
		int i = 0;
		while (true) {
			int colX = startX + i * dx;
			int colY = startY + i * dy;
			if (!field.inBounds(colX, colY)) break;
			columns.add(field.getColumn(colX, colY));
			i++;
		}
		Chip[][] slice = new Chip[columns.size()][field.dimY];
		for (int j = 0; j < i; j++) {
			slice[j] = columns.get(j);
		}
		return new FieldSlice(slice, field.winLength);
	}

}
