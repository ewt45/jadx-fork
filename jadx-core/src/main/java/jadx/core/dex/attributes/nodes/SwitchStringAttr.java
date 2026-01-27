package jadx.core.dex.attributes.nodes;

import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.List;

import jadx.api.plugins.input.data.attributes.IJadxAttrType;
import jadx.api.plugins.input.data.attributes.IJadxAttribute;
import jadx.core.dex.attributes.AType;
import jadx.core.dex.nodes.BlockNode;

/**
 * when switch(str) is compiled to smali, the first switch(hashcode) could become ifBlocks.
 * This attr is added to method.
 */
public class SwitchStringAttr implements IJadxAttribute {
	// each item is a case in 2nd switch
	private final List<Case> casesIn2ndSwitch = new ArrayList<>();
	private final BlockNode secondSwitchBlock;

	public SwitchStringAttr(BlockNode secondSwitchBlock) {
		this.secondSwitchBlock = secondSwitchBlock;
	}

	/**
	 * return 2nd switch's case, by num case key
	 */
	public @NotNull SwitchStringAttr.Case getCaseByNum(int num) {
		for (Case data : casesIn2ndSwitch) {
			if (data.getNumKeyIn2ndSwitch() == num) {
				return data;
			}
		}
		Case data = new Case(num);
		casesIn2ndSwitch.add(data);
		return data;
	}

	@Override
	public IJadxAttrType<? extends IJadxAttribute> getAttrType() {
		return AType.SWITCH_STRING;
	}

	@Override
	public String toString() {
		StringBuilder s = new StringBuilder("SWITCH_STRING");
		for (Case data : casesIn2ndSwitch) {
			s.append("\n ").append(data);
		}
		return s.toString();
	}

	public List<Case> getAllCases() {
		return casesIn2ndSwitch;
	}

	public static final class Case {
		// 2nd switch's case key
		private final int numKeyIn2ndSwitch;
		// corresponding strings acquired from 1st switch
		private final List<String> strings = new ArrayList<>();

		public Case(int numKeyIn2ndSwitch) {
			this.numKeyIn2ndSwitch = numKeyIn2ndSwitch;
		}

		public int getNumKeyIn2ndSwitch() {
			return numKeyIn2ndSwitch;
		}

		public void addStr(String str) {
			if (str != null) {
				strings.add(str);
			}
		}

		public List<String> getStrs() {
			return strings;
		}

		@Override
		public String toString() {
			return numKeyIn2ndSwitch + " -> " + strings;
		}
	}
}
