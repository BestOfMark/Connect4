package client.player;

import java.awt.Point;
import java.util.ArrayList;

import game.BoundedField;
import game.Chip;
import game.Field;

public class Yuno extends ComputerPlayer {

	/**
	 * The naive AI is used to check if either the opponent or this AI himself can win in just one move.
	 */
	//@ invariant dumbAISelf != null;
	//@ invariant dumbAIOpponent != null;
	private NaiveAI dumbAISelf, dumbAIOpponent;
	
	/**
	 * Sets the priority of this AI. A value of 0.0 means the AI will only go for his own win, without blocking the opponent.
	 * Not including situations where the opponent can win in the next move. A value of 1.0 means the AI is full defensive and
	 * will only try to block the opponent. Except for instant-win opportunities.
	 */
	//@ invariant prudence >= 0 && prudence <= 1;
	private double prudence;
	
	/**
	 * Create the <q>Yuno</q> computer player, which is smarter than the <code>Naive AI</code>. Yuno looks for the move that will
	 * result in the most potential. Potential is defined in the <code>FieldSlice</code> class.
	 * @param username the username of this (computer) player, that will be sent to the server
	 * @param chip the chip of this (computer) player
	 * @param prudence  sets the priority of this AI. A value of 0.0 means the AI will only go for his own win, without blocking the opponent.
	 * Not including situations where the opponent can win in the next move. A value of 1.0 means the AI is full defensive and
	 * will only try to block the opponent. Except for instant-win opportunities.
	 */
	//@ requires chip != null;
	//@ requires prudence >= 0 && prudence <= 1;
	public Yuno(String username, Chip chip, double prudence) {
		super(username, chip);
		dumbAISelf = new NaiveAI("dumbSelf", chip);
		dumbAIOpponent = new NaiveAI("dumbOpponent", chip.other());
		this.prudence = prudence;
	}

	@Override
	public Point getMove(Field field) {
		//Check for an istant win
		Point instantWinMove = dumbAISelf.instaWin(field);
		if (instantWinMove != null) {
			System.out.println("Instantwin");
			return instantWinMove;
		}
		
		Point mustBlock = dumbAIOpponent.instaWin(field);
		if (mustBlock != null) {
			System.out.println("MustBlock");
			return mustBlock;
		}
		
		//Calculate potential for self
		double[][] potentials = calculateMovePotentials(field, chip);
		//Calculate potential for opponent
		double[][] dangers = calculateMovePotentials(field, chip.other());
		
		//No columns that are full should be chosen
		ArrayList<Point> fullColumnIllegals = new ArrayList<>();
		for (int x = 0; x < field.dimX; x++) {
			for (int y = 0; y < field.dimY; y++) {
				if (field.columnFull(x, y)) fullColumnIllegals.add(new Point(x,y));
			}
		}
		
		//Think one step ahead
		boolean instantwin = false;
		ArrayList<Point> dumbMovesIllegals = new ArrayList<>();
		dumbMovesIllegals.addAll(fullColumnIllegals);
		Point move;
		do {
			//Determine the best move
			move = bestMove(field, potentials, dangers, dumbMovesIllegals);
			
			//If there is no way to escape a dumb move. Make the best dumb move
			if (move == null) return bestMove(field, potentials, dangers, fullColumnIllegals);
			
			//Simulate the best move
			Field moveSimulatedField = field.deepCopy();
			moveSimulatedField.addChip(chip, move.x, move.y);
			
			//Check if an instant win can be obtained by the opponent
			Point opponentMove = dumbAIOpponent.instaWin(moveSimulatedField);
			if (opponentMove != null) {
				//The opponent can now instantly win so add this move to the 'dumb' moves and reiterate.
				instantwin = true;
				dumbMovesIllegals.add(move);
			}
		} while (instantwin);
		return move;
	}
	
	/**
	 * Calculate the best moves in terms of the net potential. Which is the difference between the potential and danger (potential
	 * of the opponent). The prudence factor sets the weight of the potential and the danger in the calculation of the netto potential.
	 * @param field a copy of the current playing field
	 * @param potentials the potential for the computer player self
	 * @param dangers the potential of the opponent
	 * @param illegals the moves that should be discarded, because they are either illegal (the column is full) or they result in an
	 * instant win for the opponent.
	 * @return a java.awt.Point representing the best move in terms of net potential.
	 */
	private Point bestMove(Field field, double[][] potentials, double[][] dangers, ArrayList<Point> illegals) {
		//These two values store the highest encountered net potential and the corresponding move
		Point bestMove = null;
		double maxProfit = Integer.MIN_VALUE;
		
		//Iterate over all possible moves
		for (int x = 0; x < field.dimX; x++) {
			for (int y = 0; y < field.dimY; y++) {
				Point move = new Point(x, y);
				
				//Discard move if it is an illegal move
				if (illegals.contains(move)) continue;
				
				//Calculate the net potential using the prudence factor
				double netPot = (1.0D - prudence) * potentials[x][y] - prudence * dangers[x][y];
				
				//Detect if this is the highest net potential as of yet
				if (netPot > maxProfit) {
					//Highest net potential as of yet so overwrite the old highest
					bestMove = move;
					maxProfit = netPot;
				}
			}
		}
		
		//Highest move in terms of net profit is returned
		return bestMove;
	}
	
	/**
	 * Calculate the potential of all possible moves for a certain colour <code>Chip</code>.
	 * @param field a copy of the current playing field
	 * @param c the chip for which the potential is to be calculated
	 * @return an 2-dim array in which the potential for every possible move is stored.
	 */
	private double[][] calculateMovePotentials(Field field, Chip c) {
		double[][] potentials = new double[field.dimX][field.dimY];
		
		//Iterate over all possible moves
		for (int x = 0; x < field.dimX; x++) {
			for (int y = 0; y < field.dimY; y++) {
				//Make a copy of the field and add a chip to the copy
				Field fieldCopy = field.deepCopy();
				if (!field.columnFull(x, y)) {
					//Chip can be added at these coordinates
					fieldCopy.addChip(c, x, y);
					
					//Now calculate the potential of this move
					potentials[x][y] = totalPotential(field, c);
				} else {
					//The column is full so the potential is nil.
					potentials[x][y] = 0;
				}
			}
		}
		return potentials;
	}
	
	/**
	 * Calculate the potential of a certain field.
	 * @param field the field for which the potential is to be calculated
	 * @param c the chip for which the potential is to be calculated
	 * @return the potential of the given field
	 */
	private double totalPotential(Field field, Chip c) {
		//Initially potential is nil
		double potential = 0;
		
		//The field is sliced in four 2D slices and for those the potentials are summed
		//For all four different slices. All possible slices are iterated over
		
		//Vertical slices
		for (int x = 0; x < field.dimX; x++) {
			//Add the potential of the so-called vertical slice. The vertical slice is parallel to the y-axis.
			//Only in this slice the vertical sequence potential is calculated (a sequence along the z-axis) to avoid multiple counts
			potential += sliceField(field, x, 0, 0, 1).calculatePotential(c, true);
		}
		
		//Horizontal slices (parallel to the x-axis)
		for (int y = 0; y < field.dimY; y++) {
			potential += sliceField(field, 0, y, 1, 0).calculatePotential(c, false);
		}
		
		//Rutger slices (parallel to the surface x = -y
		for (int x = 0; x < field.dimX; x++) {
			potential += sliceField(field, x, 0, -1, 1).calculatePotential(c, false);
		}
		for (int y = 1; y < field.dimY; y++) {
			potential += sliceField(field, field.dimX - 1, y, -1, 1).calculatePotential(c, false);
		}
		
		//Mark slices (parallel to the surface x = y
		for (int x = 0; x < field.dimX; x++) {
			potential += sliceField(field, x, 0, 1, 1).calculatePotential(c, false);
		}
		for (int y = 1; y < field.dimY; y++) {
			potential += sliceField(field, 0, y, 1, 1).calculatePotential(c, false);
		}
		
		//Return the summed potential
		return potential;
	}

	/**
	 * Slice a 2D field out of the actual 3D field.
	 * @param field a copy of the 3D field
	 * @param startX the starting x-coordinate where the slice starts
	 * @param startY the starting y-coordinate where the slice starts
	 * @param dx the x-direction of the slice vector
	 * @param dy the y-direction of the slice vector
	 * @return a <code>FieldSlice</code> object representing the 2D slice
	 */
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
	
	
	//TESTING GOES HERE
	
	
	public static void main(String[] args) {
		Field field = new BoundedField(4, 4, 4, 4);
		//First row
		field.addChip(Chip.YELLOW, 0, 0);
		field.addChip(Chip.YELLOW, 3, 0);
		//Second row
		field.addChip(Chip.RED, 0, 1);
		//Third row
		field.addChip(Chip.YELLOW, 1, 2);
		//Fourth row
		field.addChip(Chip.RED, 0, 3);
		field.addChip(Chip.YELLOW, 0, 3);
		field.addChip(Chip.RED, 1, 3);
//		field.addChip(Chip.RED, 3, 3);
		
		System.out.println(field.toString());
		
		Yuno yuno = new Yuno("Yuno", Chip.RED, 0.5D);
		
		FieldSlice fs = yuno.sliceField(field, 3, 0, -1, 1);
		System.out.println(fs);
		
		System.out.println(yuno.getMove(field));
	}

}
