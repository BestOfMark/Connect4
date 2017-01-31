package client.player;

import java.awt.Point;
import java.util.ArrayList;

import game.BoundedField;
import game.Chip;
import game.Field;

public class Yuno extends ComputerPlayer {

	private NaiveAI dumbAISelf, dumbAIOpponent;
	private double prudence;
	
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
		if (instantWinMove != null) return instantWinMove;
		
		double[][] potentials = calculateMovePotentials(field, chip);
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
				instantwin = true;
				dumbMovesIllegals.add(move);
			}
		} while (instantwin);
		return move;
	}
	
	private Point bestMove(Field field, double[][] potentials, double[][] dangers, ArrayList<Point> illegals) {
		Point bestMove = null;
		double maxProfit = Integer.MIN_VALUE;
		
		for (int x = 0; x < field.dimX; x++) {
			for (int y = 0; y < field.dimY; y++) {
				Point move = new Point(x, y);
				if (illegals.contains(move)) continue;
				double profit = (1.0D - prudence) * potentials[x][y] - prudence * dangers[x][y];
				if (profit > maxProfit) {
					bestMove = move;
					maxProfit = profit;
				}
			}
		}
		
		return bestMove;
	}
	
	private double[][] calculateMovePotentials(Field field, Chip c) {
		double[][] potentials = new double[field.dimX][field.dimY];
		for (int x = 0; x < field.dimX; x++) {
			for (int y = 0; y < field.dimY; y++) {
				Field fieldCopy = field.deepCopy();
				if (!field.columnFull(x, y)) {
					fieldCopy.addChip(c, x, y);
					potentials[x][y] += totalPotential(field, c);
				} else {
					potentials[x][y] = 0;
				}
			}
		}
		return potentials;
	}
	
	private double totalPotential(Field field, Chip c) {
		double potential = 0;
		
		//Vertical slices
		for (int x = 0; x < field.dimX; x++) {
			potential += sliceField(field, x, 0, 0, 1).calculatePotential(c, true);
		}
		
		//Horizontal slices
		for (int y = 0; y < field.dimY; y++) {
			potential += sliceField(field, 0, y, 1, 0).calculatePotential(c, false);
		}
		
		//Rutger slices
		for (int x = 0; x < field.dimX; x++) {
			potential += sliceField(field, x, 0, -1, 1).calculatePotential(c, false);
		}
		for (int y = 1; y < field.dimY; y++) {
			potential += sliceField(field, field.dimX - 1, y, -1, 1).calculatePotential(c, false);
		}
		
		//Mark slices
		for (int x = 0; x < field.dimX; x++) {
			potential += sliceField(field, x, 0, 1, 1).calculatePotential(c, false);
		}
		for (int y = 1; y < field.dimY; y++) {
			potential += sliceField(field, 0, y, 1, 1).calculatePotential(c, false);
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
		field.addChip(Chip.RED, 3, 3);
	}

}
