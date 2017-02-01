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
		board[x][y][columnHeight(x, y)] = c;
		setChanged();
		notifyObservers();
	}

	@Override
	public boolean columnFull(int x, int y) {
		return columnHeight(x, y) == dimZ;
	}

	@Override
	public int columnHeight(int x, int y) {
		for (int z = 0; z < dimZ; z++) {
			if (board[x][y][z] == null) {
				return z;
			}
		}
		return dimZ;
	}

	/**
	 * Checks if a player has a sequence of at least the winning length somewhere in 
	 * the field in some direction.
	 * @param c The chip associated to the player
	 * @return <code>true</code> if such a sequence has been found in at least one 
	 * of all the possible directions,
	 * <code>false</code> otherwise.
	 */
	//@ requires c != null;
	@Override
	public boolean checkWin(Chip c) {
		for (int x = 0; x < dimX; x++) {
			for (int y = 0; y < dimY; y++) {
				for (int z = 0; z < dimZ; z++) {
					if (
							trace(c, x, y, z, 0, 0, 1) || 
							trace(c, x, y, z, 0, 1, 0) || 
							trace(c, x, y, z, 0, 1, 1) || 
							trace(c, x, y, z, 1, 0, 0) ||
							trace(c, x, y, z, 1, 0, 1) ||
							trace(c, x, y, z, 1, 1, 0) ||
							trace(c, x, y, z, 1, 1, 1) ||
					
							trace(c, x, y, z, 0, -1, 1) ||
							trace(c, x, y, z, 1, -1, 1) ||
							trace(c, x, y, z, 1, -1, 0) ||
							
							trace(c, x, y, z, -1, 0, 1) ||
							trace(c, x, y, z, -1, -1, 1) ||
							trace(c, x, y, z, -1, -1, 0) ||
					
							trace(c, x, y, z, -1, 0, 1) ||
							trace(c, x, y, z, -1, 1, 1) ||
							trace(c, x, y, z, -1, 1, 0)) {
						return true;
					}
				}
			}
		}
		return false;
	}
	
	/**
	 * Checks for a winning sequence starting from a point <code>(startX, startY, startZ)</code> 
	 * running towards a given direction given by a trace vector <code>[dx, dy, dz]</code>.
	 * @param c the <code>Chip</code> for which a winning sequence length is checked.
	 * @param startX the x-coordinate of the starting point.
	 * @param startY the y-coordinate of the starting point.
	 * @param startZ the z-coordinate of the starting point.
	 * @param dx the x-component of the trace vector.
	 * @param dy the y-component of the trace vector.
	 * @param dz the z-component of the trace vector.
	 * @return <code>true</code> if a sequence of the winning length has been found, 
	 * <code>false</code> otherwise.
	 */
	//@ requires c != null;
	//@ requires dx != 0 || dy != 0 || dz != 0;
	private boolean trace(Chip c, int startX, int startY, int startZ, int dx, int dy, int dz) {
		for (int i = 0; i < winLength; i++) {
			int currX = startX + i * dx;
			int currY = startY + i * dy;
			int currZ = startZ + i * dz;
			if (currZ < 0 || currZ >= dimZ || !inBounds(currX, currY)) {
				return false;
			}
			if (board[currX][currY][currZ] != c) {
				return false;
			}
		}
		return true;
	}
	
	@Override
	public BoundedField deepCopy() {
		BoundedField copy = new BoundedField(dimX, dimY, dimZ, winLength);
		for (int i = 0; i < dimX; i++) {
			for (int j = 0; j < dimY; j++) {
				for (int k = 0; k < columnHeight(i, j); k++) {
					copy.addChip(board[i][j][k], i, j);
				}
			}
		}
		return copy;
	}

	private static final char EMPTY_SPACE = '-';
	private static final String ROOM_BETWEEN_SLICES = "    ";
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder("Textual overview of the board:\n");
		sb.append("x -->\n");
		for (int y = 0; y < dimY; y++) {
			for (int z = 0; z < dimZ; z++) {
				for (int x = 0; x < dimX; x++) {
					if (board[x][y][z] != null) {
						sb.append(board[x][y][z].getCharacter());
					} else {
						sb.append(EMPTY_SPACE);
					}
					if (x < dimX - 1) {
						sb.append(" ");
					}
				}
				sb.append(ROOM_BETWEEN_SLICES);
			}
			if (y < dimY - 1) {
				sb.append('\n');
			}
		}
		sb.append('\n');
		for (int z = 0; z < dimZ; z++) {
			for (int x = 0; x < dimX - 3; x++) {
				sb.append(" ");
			}
			sb.append("z=" + z);
			for (int x = 0; x < dimX - 1; x++) {
				sb.append(" ");
			}
			sb.append(ROOM_BETWEEN_SLICES);
		}
		return sb.toString();
	}

	@Override
	public boolean checkFull() {
		for (int x = 0; x < dimX; x++) {
			for (int y = 0; y < dimY; y++) {
				if (!columnFull(x, y)) {
					return false;
				}
			}
		}
		return true;
	}
	
	@Override
	public Chip[] getColumn(int colX, int colY) {
		return board[colX][colY];
	}
}
