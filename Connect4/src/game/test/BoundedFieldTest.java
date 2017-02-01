package game.test;

import org.junit.Before;
import org.junit.Test;

import game.BoundedField;
import game.Chip;
import org.junit.Assert;

public class BoundedFieldTest {

	private static final int WIN = 4;
	private static final int BF1_X = 4, BF1_Y = 4, BF1_Z = 4;
	private static final int BF2_X = 4, BF2_Y = 4, BF2_Z = 4;
	private BoundedField bf1, bf2;
	private Chip c1, c2;
	
	@Before
	public void setUp() throws Exception {
		bf1 = new BoundedField(BF1_X, BF1_Y, BF1_Z, WIN);
		bf2 = new BoundedField(BF2_X, BF2_Y, BF2_Z, WIN);
		c1 = Chip.RED;
		c2 = Chip.YELLOW;
		for (int z = 0; z < BF2_Z; z++) {
			bf2.addChip(c1, 0, 0);
		}
		for (int z = 0; z < BF2_Z - 1; z++) {
			bf2.addChip(c2, BF2_X - 1, BF2_Y - 1);
		}
	}

	@Test
	public void addChip() {
		bf1.addChip(c1, 0, 0);
		Assert.assertEquals(1, bf1.columnHeight(0, 0));
		bf1.addChip(c2, 0, 0);
		Assert.assertEquals(2, bf1.columnHeight(0, 0));
		Assert.assertFalse(bf2.columnFull(BF2_X - 1, BF2_Y - 1));
		bf2.addChip(c1, BF2_X - 1, BF2_Y - 1);
		Assert.assertTrue(bf2.columnFull(BF2_X - 1, BF2_Y - 1));
	}
	
	@Test
	public void inBounds() {
		for (int x = 0; x < BF1_X; x++) {
			for (int y = 0; y < BF1_Y; y++) {
				Assert.assertTrue(bf1.inBounds(x, y));
			}
		}
		Assert.assertFalse(bf1.inBounds(0, -1));
		Assert.assertFalse(bf1.inBounds(-1, 0));
		Assert.assertFalse(bf1.inBounds(-1, -1));
		Assert.assertFalse(bf1.inBounds(BF1_X, BF1_Y));
	}

	@Test
	public void columnFull() {
		Assert.assertFalse(bf1.columnFull(0, 0));
		Assert.assertTrue(bf2.columnFull(0, 0));
		Assert.assertFalse(bf2.columnFull(BF2_X - 1, BF2_Y - 1));
	}

	@Test
	public void columnHeight() {
		for (int x = 0; x < BF1_X; x++) {
			for (int y = 0; y < BF1_Y; y++) {
				Assert.assertEquals(0, bf1.columnHeight(0, 0));
			}
		}
		Assert.assertEquals(BF2_Z, bf2.columnHeight(0, 0));
		Assert.assertEquals(BF2_Z - 1, bf2.columnHeight(BF2_X - 1, BF2_Y - 1));
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
