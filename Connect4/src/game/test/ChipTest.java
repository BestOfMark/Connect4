package game.test;

import game.Chip;

public class ChipTest {

	public static void main(String[] args) {
		Chip c = Chip.RED;
		System.out.println(c.toString());
		Chip c2 = c.other();
		System.out.println(c2.toString());
	}

}
