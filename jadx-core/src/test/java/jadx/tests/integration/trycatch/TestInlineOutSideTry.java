package jadx.tests.integration.trycatch;

import java.util.regex.Pattern;

import org.junit.jupiter.api.Test;

import jadx.NotYetImplemented;
import jadx.tests.api.IntegrationTest;
import jadx.tests.api.utils.assertj.JadxAssertions;

public class TestInlineOutSideTry extends IntegrationTest {

	private static class TestCls {
		private void test() {
			try {
				while (true) {
					if (getDouble() > 0.5) {
						break;
					}
				}
			} catch (Exception e) {
				System.out.println("exception");
			}
		}

		private double getDouble() throws Exception {
			double d = Math.random();
			if (d < 0.1) {
				throw new Exception("d < 0.1");
			}
			return d;
		}
	}

	private static class TestCls2 {
		private void test() {
			while (true) {
				try {
					if (getDouble() > 0.5) {
						break;
					}
				} catch (Exception e) {
					System.out.println("exception");
				}
			}
		}

		private double getDouble() throws Exception {
			double d = Math.random();
			if (d < 0.1) {
				throw new Exception("d < 0.1");
			}
			return d;
		}
	}

	@Test
	public void test() {
		JadxAssertions.assertThat(getClassNode(TestCls.class))
				.code()
				.containsPattern(Pattern.compile("try(.*?)getDouble(.*?)catch", Pattern.DOTALL));
	}

	@Test
	@NotYetImplemented
	public void test2() {
		// double d maybe not initialized before using in if condition
		JadxAssertions.assertThat(getClassNode(TestCls2.class))
				.code();
	}
}
