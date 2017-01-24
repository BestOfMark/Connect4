package game;

public class BoundedField extends Field {

	/**
	 * The game state is stored in the <code>Board</code> object. This is a three-dimensional 
	 * array of type <code>Chip</code>. Both players have a unique type of chip defined in the 
	 * enum <code>Chip</code>.
	 */
	//@ invariant board != null;
	protected Chip[][][] board;
	
	public BoundedField(int sizeX, int sizeY, int sizeZ, int winLength) {
		super(sizeX, sizeY, sizeZ, winLength);
		board = new Chip[sizeX][sizeY][sizeZ];
	}

	@Override
	public void addChip(Chip c, int x, int y) {
		board[x][y][columnHeight(x,y)] = c;
	}

	@Override
	public boolean columnFull(int x, int y) {
		return columnHeight(x, y) == dimZ;
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
		return false;
	}
	
	private boolean traceRay(Chip c, int startX, int startY, int startZ, int dx, int dy, int dz) {
		for (int i = 0; i < winLength; i++) {
			int currX = startX + i * dx;
			int currY = startY + i * dx;
			int currZ = startX + i * dx;
			if (currZ >= dimZ || !inBounds(currX, currY)) return false;
			if (board[currX][currY][currZ] != c) return false;
		}
		return true;
	}
	
	/**
	 * Returns an unlinked copy of the field. Changing the state of the copy will not change the
	 * state of the original.
	 * @return a copy of the field.
	 */
	/*@ pure */ public BoundedField deepCopy() {
		BoundedField copy = new BoundedField(dimX, dimY, dimZ, winLength);
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
		StringBuilder sb = new StringBuilder("Textual overview of the board:\n");
		for (int y = 0; y < dimY; y++) {
			for (int x = 0; x < dimX; x++) {
				sb.append(String.format("%2d", columnHeight(x, y)));
				if (x < dimX - 1) sb.append(" ");
			}
			if (y < dimY - 1) sb.append('\n');
		}
		return sb.toString();
	}
}
