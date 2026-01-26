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
	private final List<SwitchStringData> casesIn2ndSwitch = new ArrayList<>();
	private final BlockNode secondSwitchBlock;

	public SwitchStringAttr(BlockNode secondSwitchBlock) {
		this.secondSwitchBlock = secondSwitchBlock;
	}

	/**
	 * return 2nd switch's case, by num case key
	 */
	public @NotNull SwitchStringData getCaseByNum(Integer num) {
		for (SwitchStringData data : casesIn2ndSwitch) {
			if (data.getNumKeyIn2ndSwitch().contains(num)) {
				return data;
			}
		}
		SwitchStringData data = new SwitchStringData();
		data.getNumKeyIn2ndSwitch().add(num);
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
		for (SwitchStringData data : casesIn2ndSwitch) {
			s.append("\n ").append(data);
		}
		return s.toString();
	}

	public static final class SwitchStringData {
		// 2nd switch's case key
		private final List<Integer> numKeyIn2ndSwitch = new ArrayList<>();
		// corresponding strings acquired from 1st switch
		private final List<String> strings = new ArrayList<>();

		public List<Integer> getNumKeyIn2ndSwitch() {
			return numKeyIn2ndSwitch;
		}

		public void addStr(String str) {
			if (str != null) {
				strings.add(str);
			}
		}

		@Override
		public String toString() {
			return numKeyIn2ndSwitch + " -> " + strings;
		}
	}
}
