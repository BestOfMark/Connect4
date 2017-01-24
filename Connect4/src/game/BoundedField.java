package game;

public class BoundedField extends Field {

	/**
	 * The game state is stored in the <code>Board</code> object. This is a three-dimensional 
	 * array of type <code>Chip</code>. Both players have a unique type of chip defined in the 
	 * enum <code>Chip</code>.
	 */
	//@ invariant board != null;
	protected Chip[][][] board;
	
	public BoundedField(int sizeX, int sizeY, int sizeZ) {
		super(sizeX, sizeY, sizeZ);
		// TODO Auto-generated constructor stub
	}

	@Override
	public void addChip(Chip c, int x, int y) {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean columnFull(int x, int y) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public int columnHeight(int x, int y) {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public boolean checkWin(Chip c) {
		// TODO Auto-generated method stub
		return false;
	}
	
	/**
	 * Returns an unlinked copy of the field. Changing the state of the copy will not change the
	 * state of the original.
	 * @return a copy of the field.
	 */
	/*@ pure */ public Field deepCopy() {
		return null;
	}

	@Override
	public String toString() {
		return super.toString();
	}
}
