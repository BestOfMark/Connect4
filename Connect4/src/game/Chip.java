package game;

public enum Chip {
	RED("red"), YELLOW("yellow");
	
	private String colour;
	
	private Chip(String s) {
		this.colour = s;
	}
	
	public Chip other() {
		return this == RED ? YELLOW : RED;
	}
	
	@Override
	public String toString() {
		return "Chip color = " + colour;
	}
}
