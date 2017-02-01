package client.player;

import game.Chip;

public class FieldSlice {

	private Chip[][] field;
	private final int dimHor, dimVert;
	private final int winSize;
	
	/**
	 * Creates an empty field slice with the given height and width.
	 * @param width the width of the field slice
	 * @param height the height of the field slice
	 * @param winSize the sequence length needed to win the game
	 */
	public FieldSlice(int width, int height, int winSize) {
		this.dimHor = width;
		this.dimVert = height;
		field = new Chip[dimHor][dimVert];
		this.winSize = winSize;
	}
	
	/**
	 * Creates a <code>FieldSlice</code> with the field initialized to the given <code>Chip</code> array.
	 * @param slice the <code>Chip</code> array representing a 2D slice of the 3D field.
	 * @param winSize the sequence length needed to win the game
	 */
	public FieldSlice(Chip[][] slice, int winSize) {
		dimHor = slice.length;
		dimVert = slice[0].length;
		this.field = slice;
		this.winSize = winSize;
	}

	/**
	 * Calculates the potential of this 2D field slice.
	 * @param c the chip for which the potential is calculated
	 * @param b <code>true</code> if a vertical-sequence (along the z-axis) should be considered in the calculations.
	 * @return the potential of this field slice
	 */
	public double calculatePotential(Chip c, boolean b) {
		double potential = 0.0;
		for (int x = 0; x < dimHor; x++) {
			for (int y = 0; y < dimVert; y++) {
				//The naming of the potentials follows the same logic as explained in Yuno.java
				
				//Vertical potential
				if (b) potential += potentialTraceVertical(c, x, y);
				
				//Horizontal potential
				potential += potentialTrace(c, x, y, 1, 0);
				
				//Rutger potential
				potential += potentialTrace(c, x, y, 1, 1);
				
				//Mark potential
				potential += potentialTrace(c, x, y, -1, 1);
			}
		}
		return potential;
	}
	
	/**
	 * Check if a sequence of the win length is feasible. The easier this is to achieve the larger the potential.
	 * The more chips that have to be placed before this sequence can be completed the lower the potential.
	 * @param c the chip for which a sequence potential is calculated
	 * @param startX the x-coordinate of the first chip in the sequence
	 * @param startY the y-coordinate of the first chip in the sequence
	 * @param dx the x-component of the trace vector
	 * @param dy the y-component of the trace vector
	 * @return the potential of this sequence
	 */
	public double potentialTrace(Chip c, int startX, int startY, int dx, int dy) {
		int streak = 0;
		int foundation = 0;
		for (int i = 0; i < winSize; i++) {
			int x = startX + i * dx;
			int y = startY + i * dy;
			if (!inField(x,y) || field[x][y] != c) return 0;
			if (field[x][y] == c) streak++;
			else foundation += howManyUnderneath(x, y);
		}
		return potential(foundation, streak);
	}
	
	/**
	 * Check if a vertical sequence of the win length is feasible. The easier this is to achieve the larger the potential.
	 * The more chips that have to be placed before this sequence can be completed the lower the potential.
	 * @param c the chip for which a sequence potential is calculated
	 * @param startX the x-coordinate of the first chip in the sequence
	 * @param startY the y-coordinate of the first chip in the sequence
	 * @return the potential of this (vertical) sequence
	 */
	public double potentialTraceVertical(Chip c, int startX, int startY) {
		int streak = 0;
		if (field[startX][startY] == c.other()) {
			return 0;
		}
		int foundation = howManyUnderneath(startX, startY);
		for (int i = 0; i < winSize; i++) {
			int y = startY + i;
			if (!inField(startX, y) || field[startX][y] == c.other()) {
				return 0;
			}
			if (field[startX][y] == c) streak++;
		}
		System.out.println(foundation + ", " + streak);
		return potential(foundation, streak);
	}
	
	/**
	 * Calculate how many empty spaces (so not occupied by chips of the local player or the opponent) are underneath a 
	 * certain position in the field slice.
	 * @param xPos the x-coordinate of the position
	 * @param yPos the y-coordinate of the position
	 * @return the number of empty spaces underneath that position
	 */
	private int howManyUnderneath(int xPos, int yPos) {
		int i = 0;
		int y = yPos;
		while (true) {
			if (y < 0 || field[xPos][y] != null) break;
			y--;
			i++;
		}
		return i-1;
	}
	
	/**
	 * Check if a position is inside the field slice
	 * @param x the x-coordinate of the position
	 * @param y the y-coordinate of the position
	 * @return <code>true</code> if the position is inside the field, <code>false</code> otherwise.
	 */
	private boolean inField(int x, int y) {
		return x >= 0 && x < dimHor && y >= 0 && y < dimVert;
	}
	
	/**
	 * Calculate the potential of a possible winning sequence.
	 * @param foundation the amount of chips needed such that the chips can be actually placed on top of existing chips in the field.
	 * @param streak the amount of chips (belonging to the player for which the potential is calculated) already present in the possible 
	 * winning sequence
	 * @return a floating point number representing the sequence's potential
	 */
	private double potential(double foundation, double streak) {
		return (foundation > 0) ? 1.0D / Math.pow(foundation, 1.0D) * Math.pow(2.0D, 2.0D * streak) : Math.pow(2.0D, 2.0 * streak + 1);
	}
	
	private static final char WHITESPACE = ' ';
	private static final char EMPTYSPACE = 'O';
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder("Field slice:\n");
		for (int y = dimVert - 1; y >= 0; y--) {
			for (int x = 0; x < dimHor; x++) {
				if (field[x][y] == null) {
					sb.append(EMPTYSPACE);
				} else {
					sb.append(field[x][y].getCharacter());
				}
				if (x < dimHor - 1) {
					sb.append(WHITESPACE);
				}
			}
			sb.append("\n");
		}
		sb.append("End of field");
		return sb.toString();
	}
	
	
	//TESTING GOES HERE
	
	
	public static void main(String[] args) {
		FieldSlice fs = new FieldSlice(6, 4, 4);
		System.out.println(fs.toString());
		
		FieldSlice fs2 = new FieldSlice(new Chip[][] {
			new Chip[]{Chip.RED, Chip.RED, Chip.RED, Chip.RED}, 
			new Chip[]{Chip.RED, Chip.RED, Chip.YELLOW, Chip.YELLOW}, 
			new Chip[]{Chip.YELLOW, Chip.RED, Chip.YELLOW, Chip.RED}
		}, 4);
		System.out.println(fs2.toString());
		
		FieldSlice fs3 = new FieldSlice(new Chip[][] {
			new Chip[]{Chip.RED, Chip.RED, null, null}, 
			new Chip[]{Chip.RED, Chip.RED, Chip.YELLOW, null}, 
			new Chip[]{Chip.YELLOW, null, null, null}
		}, 4);
		System.out.println(fs3.toString());
		
		System.out.println(fs3.howManyUnderneath(2, 3));
		
		
	}
}
