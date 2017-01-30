package game;

public enum Chip {
	RED('R'), YELLOW('Y');
	
	private final char colour;
	
	/**
	 * Initialize a <code>Chip</code> with a string representation of the colour
	 * @param s
	 */
	private Chip(char c) {
		this.colour = c;
	}
	
	/**
	 * Return the <code>Chip</code> that is of the other colour than this <code>Chip</code>.
	 * @return the other <code>Chip</code>
	 */
	//@ ensures \result != null;
	public Chip other() {
		return this == RED ? YELLOW : RED;
	}
	
	/**
	 * Return a character representation of the colour of the chip.
	 * @return the first letter of the colour of the chip
	 */
	public char getCharacter() {
		return colour;
	}
	
	@Override
	public String toString() {
		return "Chip{color = " + super.toString() + ", char = " + colour + "}";
	}
}
