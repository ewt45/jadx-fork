package jadx.tests.integration.trycatch;

import org.junit.jupiter.api.Test;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;

import jadx.tests.api.IntegrationTest;

public class TestTryCatchInIf2 extends IntegrationTest {



	public static class TestCls2 {
//		public void test1一个catch() {
//			try {
//				System.out.println("Test");
//			} catch (ProviderException e) {
//				System.out.println("ProviderException");
//			}
//		}
//
//		// 这个是可以的
//		public void test2两个catch() {
//			try {
//				System.out.println("Test");
//			} catch (ProviderException e) {
//				System.out.println("ProviderException");
//			} catch (DateTimeException e) {
//				System.out.println("DateTimeException");
//			}
//		}
//
//		// 可以
//		public void test3一个catch两个Exception() {
//			try {
//				System.out.println("Test");
//			} catch (ProviderException | DateTimeException e) {
//				System.out.println("ProviderException | DateTimeException");
//			}
//		}
//
//		// 不可以
//		public void test4两个catch两个Exception() {
//			try {
//				System.out.println("Test");
//			} catch (ProviderException | DateTimeException e) {
//				System.out.println("ProviderException | DateTimeException");
//			} catch (java.security.InvalidParameterException e) {
//				System.out.println("InvalidParameterException");
//			}
//		}
//
//		public void test5() {
//			System.out.println("Before");
//			try {
//				System.out.println("Test");
//				System.out.println("Test2");
//			} catch (ProviderException e) {
//				System.out.println("ProviderException");
//				System.out.println("ProviderException2");
//			} finally {
//				System.out.println("Finally");
//			}
//			System.out.println("After");
//		}
//
//		public void test6() {
//			try {
//				System.out.println("try");
//			} catch (RuntimeException e) {
//				System.out.println("catch");
//			} finally {
//				System.out.println("finally");
//			}
//		}

		public void test7() throws IOException {
			try (BufferedReader br = new BufferedReader(new FileReader("file"))) {
				br.readLine();
			}
		}
	}

	@Test
	public void test2() {
		System.out.println("看看代码：\n" + getClassNode(TestCls2.class).decompile().getCodeStr());
	}


	public static class TestCls3 {
		// 又发现一个报错的。。。
//		public void test2(boolean flag) {
//			String str = "";
//			boolean flag2 = true;
//			while (flag2) {
//				try {
//					str = toString();
//				} catch (Exception e) {
//					str = "error";
//					break;
//				}
//				flag2 = Math.random() > 0.5;
//			}
//			System.out.println(str);
//		}

		public void onCreate(Class<?> cls) {
			Object obj = null;
			if (cls != null) {
				try {
					obj = cls.getDeclaredConstructor().newInstance();
				} catch (Exception e) {
					System.out.println("error");
				}
			}
			System.out.println("obj = "+ obj);
		}
	}

	@Test
	public void test3() {
		// 禁用 debugInfo，否则有很多行额外信息，代码会正确复原
		noDebugInfo();
		// java 8,9 都正常，10 开始就漏掉 catch 中的初始化了
		useTargetJavaVersion(10);
//		getArgs().setCfgOutput(true);
		// 另：原代码不管是在开头 null 还是 catch 和 else 里 null, java 8, 9 反编译后都是 开头 null,
		// 然后 java 10 反编译后都是只有 else 里一个 null
		System.out.println("看看代码：\n" + getClassNode(TestCls3.class).getCode().toString());
	}
}
