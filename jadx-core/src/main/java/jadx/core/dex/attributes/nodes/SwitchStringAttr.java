package jadx.core.dex.attributes.nodes;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.jetbrains.annotations.NotNull;

import jadx.api.plugins.input.data.attributes.IJadxAttrType;
import jadx.api.plugins.input.data.attributes.IJadxAttribute;
import jadx.core.dex.attributes.AType;
import jadx.core.dex.instructions.args.RegisterArg;
import jadx.core.dex.nodes.BlockNode;

/**
 * when switch(str) is compiled to smali, the first switch(hashcode) could become ifBlocks.
 * This attr is added to method.
 */
public class SwitchStringAttr implements IJadxAttribute {
	private final List<Case> casesOf2ndSwitch = new ArrayList<>();
	private final BlockNode secondSwitchBlock;
	// stores the target string hash code
	private RegisterArg targetStrHashArg = null;
	// stores the target string object
	private RegisterArg targetStrArg = null;
	// first switch (if). key: case hashcode or DEFAULT,
	// value: case container. contains str.equals() compare and num assign
	private final Map<Object, BlockNode> strCompareMap = new HashMap<>();

	public SwitchStringAttr(BlockNode secondSwitchBlock) {
		this.secondSwitchBlock = secondSwitchBlock;
	}

	/**
	 * return 2nd switch's case, by num case key
	 */
	public @NotNull SwitchStringAttr.Case getCaseByNum(int num) {
		for (Case data : casesOf2ndSwitch) {
			if (data.getNumKeyIn2ndSwitch() == num) {
				return data;
			}
		}
		Case data = new Case(num);
		casesOf2ndSwitch.add(data);
		return data;
	}

	@Override
	public IJadxAttrType<? extends IJadxAttribute> getAttrType() {
		return AType.SWITCH_STRING;
	}

	@Override
	public String toString() {
		StringBuilder s = new StringBuilder("SWITCH_STRING");
		for (Case data : casesOf2ndSwitch) {
			s.append("\n ").append(data);
		}
		return s.toString();
	}

	public List<Case> getAllCases() {
		return casesOf2ndSwitch;
	}

	public RegisterArg getTargetStrHashArg() {
		return targetStrHashArg;
	}

	public void setTargetStrHashArg(RegisterArg targetStrHashArg) {
		this.targetStrHashArg = targetStrHashArg;
	}

	public RegisterArg getTargetStrArg() {
		return targetStrArg;
	}

	public void setTargetStrArg(RegisterArg targetStrArg) {
		this.targetStrArg = targetStrArg;
	}

	public Map<Object, BlockNode> getStrCompareMap() {
		return strCompareMap;
	}

	public BlockNode getSecondSwitchBlock() {
		return secondSwitchBlock;
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
