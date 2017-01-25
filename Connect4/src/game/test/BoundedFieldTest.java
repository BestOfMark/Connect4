package game.test;

import org.junit.Before;
import org.junit.Test;

import game.BoundedField;
import game.Chip;
import org.junit.Assert;

public class BoundedFieldTest {

	private static final int WIN = 4;
	private static final int bf1X = 4, bf1Y = 4, bf1Z = 4;
	private static final int bf2X = 4, bf2Y = 4, bf2Z = 4;
	private BoundedField bf1, bf2;
	private Chip c1, c2;
	
	@Before
	public void setUp() throws Exception {
		bf1 = new BoundedField(bf1X,bf1Y,bf1Z, WIN);
		bf2 = new BoundedField(bf2X,bf2Y,bf2Z, WIN);
		c1 = Chip.RED;
		c2 = Chip.YELLOW;
		for (int z = 0; z < bf2Z; z++) {
			bf2.addChip(c1, 0, 0);
		}
		for (int z = 0; z < bf2Z - 1; z++) {
			bf2.addChip(c2, bf2X - 1, bf2Y - 1);
		}
	}

	@Test
	public void addChip() {
		bf1.addChip(c1, 0, 0);
		Assert.assertEquals(1, bf1.columnHeight(0, 0));
		bf1.addChip(c2, 0, 0);
		Assert.assertEquals(2, bf1.columnHeight(0, 0));
		Assert.assertFalse(bf2.columnFull(bf2X - 1, bf2Y - 1));
		bf2.addChip(c1, bf2X - 1, bf2Y - 1);
		Assert.assertTrue(bf2.columnFull(bf2X - 1, bf2Y - 1));
	}
	
	@Test
	public void inBounds() {
		for (int x = 0; x < bf1X; x++) {
			for (int y = 0; y < bf1Y; y++) {
				Assert.assertTrue(bf1.inBounds(x, y));
			}
		}
		Assert.assertFalse(bf1.inBounds(0, -1));
		Assert.assertFalse(bf1.inBounds(-1, 0));
		Assert.assertFalse(bf1.inBounds(-1, -1));
		Assert.assertFalse(bf1.inBounds(bf1X, bf1Y));
	}

	@Test
	public void columnFull() {
		Assert.assertFalse(bf1.columnFull(0, 0));
		Assert.assertTrue(bf2.columnFull(0, 0));
		Assert.assertFalse(bf2.columnFull(bf2X - 1, bf2Y - 1));
	}

	@Test
	public void columnHeight() {
		for (int x = 0; x < bf1X; x++) {
			for (int y = 0; y < bf1Y; y++) {
				Assert.assertEquals(0, bf1.columnHeight(0, 0));
			}
		}
		Assert.assertEquals(bf2Z, bf2.columnHeight(0, 0));
		Assert.assertEquals(bf2Z - 1, bf2.columnHeight(bf2X - 1, bf2Y - 1));
	}

	@Test
	public void checkWin() {
		
	}
	
	@Test
	public void deepCopy() {
		bf1.addChip(Chip.RED, 0, 0);
		Assert.assertEquals(1, bf1.columnHeight(0, 0));
		BoundedField copy = bf1.deepCopy();
		Assert.assertEquals(1, copy.columnHeight(0, 0));
		copy.addChip(Chip.YELLOW, 0, 0);
		Assert.assertEquals(1, bf1.columnHeight(0, 0));
		Assert.assertEquals(2, copy.columnHeight(0, 0));
	}
	
	@Test
	public void printString() {
		System.out.println(bf1.toString());
		System.out.println(bf2.toString());
	}

}
