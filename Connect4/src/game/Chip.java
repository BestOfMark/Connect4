package game;

public enum Chip {
	RED("red"), YELLOW("yellow");
	
	private final String colour;
	
	/**
	 * Initialize a <code>Chip</code> with a string representation of the colour
	 * @param s
	 */
	private Chip(String s) {
		this.colour = s;
	}
	
	/**
	 * Return the <code>Chip</code> that is of the other colour than this <code>Chip</code>.
	 * @return the other <code>Chip</code>
	 */
	public Chip other() {
		return this == RED ? YELLOW : RED;
	}
	
	@Override
	public String toString() {
		return "Chip{color = " + colour + "}";
	}
}
