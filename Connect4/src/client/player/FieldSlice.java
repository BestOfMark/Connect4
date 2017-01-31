package client.player;

import game.Chip;

public class FieldSlice {

	private Chip[][] field;
	private final int dimHor, dimVert;
	private final int winSize;
	
	public FieldSlice(int width, int height, int winSize) {
		this.dimHor = width;
		this.dimVert = height;
		field = new Chip[dimHor][dimVert];
		this.winSize = winSize;
	}
	
	public FieldSlice(Chip[][] slice, int winSize) {
		dimHor = slice.length;
		dimVert = slice[0].length;
		this.field = slice;
		this.winSize = winSize;
	}

	public double calculatePotential(Chip c, boolean b) {
		double potential = 0.0;
		for (int x = 0; x < dimHor; x++) {
			for (int y = 0; y < dimVert; y++) {
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
	
	public double potentialTraceVertical(Chip c, int startX, int startY) {
		int streak = 0;
		int foundation = howManyUnderneath(startX, startY);
		for (int i = 0; i < winSize; i++) {
			int y = startY + i;
			if (!inField(startX,y) || field[startX][y] != c) return 0;
			if (field[startX][y] == c) streak++;
		}
		return potential(foundation, streak);
	}
	
	private int howManyUnderneath(int xPos, int yPos) {
		if (yPos == 0) return 0;
		int y = yPos;
		for (int i = 0; y >= 0; i++) {
			y = yPos - i - 1;
			if (field[xPos][y] != null) return i;
		}
		return yPos - 1;
	}
	
	private boolean inField(int x, int y) {
		return x >= 0 && x < dimHor && y >= 0 && y < dimVert;
	}
	
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
