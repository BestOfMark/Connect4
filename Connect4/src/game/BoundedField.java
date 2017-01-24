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
		board = new Chip[sizeX][sizeY][sizeZ];
	}

	@Override
	public void addChip(Chip c, int x, int y) {
		board[x][y][columnHeight(x,y)] = c;
	}

	@Override
	public boolean columnFull(int x, int y) {
		return columnHeight(x, y) == dimY;
	}

	@Override
	public int columnHeight(int x, int y) {
		for (int z = 0; z < dimZ; z++) {
			if (board[x][y][z] == null) return z;
		}
		return dimZ;
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
		Field copy = new BoundedField(dimX, dimY, dimZ);
		for (int i = 0; i < dimX; i++) {
			for (int j = 0; j < dimY; j++) {
				for (int k = 0; k < columnHeight(i,j); k++ ) {
					copy.addChip(board[i][j][k] ,i, j);
				}
			}
		}
		return copy;
	}

	@Override
	public String toString() {
		return super.toString();
	}
}
