package game;

import java.util.Observable;

public abstract class Field extends Observable {
	
	/**
	 * Field dimension
	 */
	//@ invariant dimX > 0 && dimY > 0 && dimZ > 0;
	public final int dimX, dimY, dimZ;
	
	public final int winLength;
	
	/**
	 * This is a convenience constructor for subclasses to set the dimensions of the field.
	 * @param sizeX the x dimension of the field, also known as the width.
	 * @param sizeY the y dimension of the field, also known as the depth.
	 * @param sizeZ the z dimension of the field, also known as the height. For infinite field 
	 * height this should be <code>-1</code>.
	 */
	//@ requires sizeX > 0; sizeY > 0; sizeZ > 0;
	protected Field(int sizeX, int sizeY, int sizeZ, int winLength) {
		dimX = sizeX; 
		dimY = sizeY;
		dimZ = sizeZ;
		this.winLength = winLength;
	}
	

	/**
	 * Adds the specified chip to the specified column.
	 * @param c the chip that should be added to the column.
	 * @param x the x-coordinate of the column.
	 * @param y the y-coordinate of the column.
	 */
	//@ requires inBounds(x,y);
	//@ requires !columnFull(x, y);
	//@ requires c != null;
	//@ ensures columnHeight(x, y) == \old(columnHeight(x,y)) + 1;
	abstract public void addChip(Chip c, int x, int y);
	
	/**
	 * Checks if any more chips can be added to the column.
	 * @param x the x-coordinate of the column.
	 * @param y the y-coordinate of the column.
	 * @return <code>true</code> if the amount of chips equals the height of the field.
	 * <code>false</code> if there is still room for a new chip.
	 */
	//@ requires inBounds(x,y);
	//@ ensures \result == (columnHeight(x,y) == dimY);
	/*@ pure */ abstract public boolean columnFull(int x, int y);
	
	/**
	 * Returns the amount of chips in a column.
	 * @param x the x-coordinate of the column.
	 * @param y the y-coordinate of the column.
	 * @return an integer representing the amount of chips in the column.
	 */
	//@ requires inBounds(x,y);
	/*@ pure */ abstract public int columnHeight(int x, int y);
	
	/**
	 * Checks if the coordinates for a column is within the bounds of the field.
	 * @param x the x-coordinate of the column.
	 * @param y the y-coordinate of the column.
	 * @return <code>true</code> if the specified coordinates lie within the bounds
	 * of the field, <code>false</code> otherwise.
	 */
	//@ ensures \result == (x >= 0 && x < dimX && y >= 0 && y < dimY);
	/*@ pure */ public boolean inBounds(int x, int y) {
		return x >= 0 && x < dimX && y >= 0 && y < dimY;
	}
	
	/**
	 * Check if a player associated with a certain chip has a sequence of chips that is equal
	 * or higher than the winning sequence length.
	 * @param c the chip for which the sequences should be checked.
	 * @return <code>true</code> if a sequence of at least the winning length was found, <code>
	 * false</code> otherwise.
	 */
	//@ requires c != null;
	/*@ pure */ abstract public boolean checkWin(Chip c);
	
	/**
	 * Check if the field is full, i.e. no more chips can be added to any row.
	 * @return <code>true</code> if no more chips can be added anymore, <code>
	 * false</code> otherwise.
	 */
	/*@ pure */ abstract public boolean checkFull();
	
	/**
	 * Returns an unlinked copy of the field. Changing the state of the copy will not change the
	 * state of the original.
	 * @return a copy of the field.
	 */
	/*@ pure */ abstract public Field deepCopy();
}
