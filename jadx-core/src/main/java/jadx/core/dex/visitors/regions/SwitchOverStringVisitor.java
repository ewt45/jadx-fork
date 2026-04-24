package jadx.core.dex.visitors.regions;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import org.jetbrains.annotations.Nullable;

import jadx.api.plugins.input.data.annotations.EncodedType;
import jadx.api.plugins.input.data.annotations.EncodedValue;
import jadx.api.plugins.input.data.attributes.JadxAttrType;
import jadx.core.dex.attributes.AFlag;
import jadx.core.dex.attributes.IAttributeNode;
import jadx.core.dex.attributes.nodes.CodeFeaturesAttr;
import jadx.core.dex.attributes.nodes.CodeFeaturesAttr.CodeFeature;
import jadx.core.dex.info.MethodInfo;
import jadx.core.dex.instructions.IfNode;
import jadx.core.dex.instructions.IfOp;
import jadx.core.dex.instructions.InsnType;
import jadx.core.dex.instructions.InvokeNode;
import jadx.core.dex.instructions.SwitchInsn;
import jadx.core.dex.instructions.args.InsnArg;
import jadx.core.dex.instructions.args.InsnWrapArg;
import jadx.core.dex.instructions.args.LiteralArg;
import jadx.core.dex.instructions.args.RegisterArg;
import jadx.core.dex.instructions.args.SSAVar;
import jadx.core.dex.nodes.BlockNode;
import jadx.core.dex.nodes.FieldNode;
import jadx.core.dex.nodes.IContainer;
import jadx.core.dex.nodes.IRegion;
import jadx.core.dex.nodes.InsnNode;
import jadx.core.dex.nodes.MethodNode;
import jadx.core.dex.regions.SwitchRegion;
import jadx.core.dex.visitors.AbstractVisitor;
import jadx.core.dex.visitors.JadxVisitor;
import jadx.core.utils.BlockUtils;
import jadx.core.utils.InsnRemover;
import jadx.core.utils.InsnUtils;
import jadx.core.utils.ListUtils;
import jadx.core.utils.RegionUtils;
import jadx.core.utils.exceptions.JadxException;

@JadxVisitor(
		name = "SwitchOverStringVisitor",
		desc = "Restore switch over string",
		runAfter = IfRegionVisitor.class,
		runBefore = ReturnVisitor.class
)
public class SwitchOverStringVisitor extends AbstractVisitor implements IRegionIterativeVisitor {
	private static final Integer DEFAULT_NUM_VALUE = -1;

	@Override
	public void visit(MethodNode mth) throws JadxException {
		if (!CodeFeaturesAttr.contains(mth, CodeFeature.SWITCH)) {
			return;
		}
		DepthRegionTraversal.traverseIterative(mth, this);
	}

	@Override
	public boolean visitRegion(MethodNode mth, IRegion region) {
		if (region instanceof SwitchRegion) {
			return restoreSwitchOverString(mth, (SwitchRegion) region);
		}
		return false;
	}

	private boolean restoreSwitchOverString(MethodNode mth, SwitchRegion switchRegion) {
		try {
			InsnNode swInsn = BlockUtils.getLastInsnWithType(switchRegion.getHeader(), InsnType.SWITCH);
			if (swInsn == null) {
				return false;
			}
			RegisterArg strArg = getStrHashCodeArg(swInsn.getArg(0));
			if (strArg == null) {
				return false;
			}
			int casesCount = switchRegion.getCases().size();
			boolean defaultCaseAdded = switchRegion.getCases().stream().anyMatch(SwitchRegion.CaseInfo::isDefaultCase);
			int casesWithString = defaultCaseAdded ? casesCount - 1 : casesCount;
			SSAVar strVar = strArg.getSVar();
			if (strVar.getUseCount() - 1 < casesWithString) {
				// one 'hashCode' invoke and at least one 'equals' per case
				return false;
			}

			SwitchData data = new SwitchData(mth, switchRegion);
			data.setCases(new ArrayList<>(casesCount));
			data.setStrArg(strArg);

			IContainer nextContainer = RegionUtils.getNextContainer(mth, switchRegion);
			if (nextContainer instanceof SwitchRegion) {
				data.setType(SwitchStringType.SWITCH_SWITCH);
				data.setPart2Region((SwitchRegion) nextContainer);
			} else {
				data.setType(SwitchStringType.SINGLE_SWITCH);
			}
			if (data.getType() == SwitchStringType.SWITCH_SWITCH || data.getType() == SwitchStringType.IF_SWITCH) {
				InsnNode codeSwInsn = BlockUtils.getLastInsnWithType(((SwitchRegion) nextContainer).getHeader(), InsnType.SWITCH);
				if (codeSwInsn == null || !codeSwInsn.getArg(0).isRegister()) {
					return false;
				}
				data.setNumArg((RegisterArg) codeSwInsn.getArg(0));
			}

			if (!validatePart1Region(data)) {
				return false;
			}

			if (!prepareMergedSwitchCases(data) || !replaceWithMergedSwitch(data)) {
				mth.addWarnComment("Failed to restore switch over string. Please report as a decompilation issue");
				return false;
			}
			return true;
		} catch (StackOverflowError | Exception e) {
			mth.addWarnComment("Failed to restore switch over string. Please report as a decompilation issue", e);
			return false;
		}
	}

	/**
	 * store str and num assign in switchData.getCases()
	 * validate:
	 * 1. case block is str.equals compare
	 * 2. case key is hashcode of strValue
	 * 3. compare then is num assign if SWITCH_SWITCH or IF_SWITCH
	 * @return false if it isn't switch string pattern
	 */
	private boolean validatePart1Region(SwitchData data) {
		if (data.getType() == SwitchStringType.IF_SWITCH) {
			throw new RuntimeException("stub");
		}
		SwitchRegion part1Switch = (SwitchRegion) data.getPart1Region();
		SwitchInsn swInsn = Objects.requireNonNull((SwitchInsn) BlockUtils.getLastInsnWithType(part1Switch.getHeader(), InsnType.SWITCH));
		for (int i = 0; i < swInsn.getKeys().length; i++) {
			int hashcode = swInsn.getKeys()[i];
			BlockNode caseBlock = getOnlyOneInsnBlock(swInsn.getTargetBlocks()[i]);
			IfNode ifStrEqualsInsn = (IfNode) BlockUtils.getLastInsnWithType(caseBlock, InsnType.IF);
			if (!isIfStringEqualsInsn(ifStrEqualsInsn)) {
				return false;
			}
			do {
				InsnNode strEqualsInsn = Objects.requireNonNull(InsnUtils.getWrappedInsn(ifStrEqualsInsn.getArg(0)));
				InsnArg strArg = strEqualsInsn.getArg(0);
				InsnArg valArg = strEqualsInsn.getArg(1);
				Object strValue = InsnUtils.getConstValueByArg(data.getMth().root(), valArg);
				if (!data.getStrArg().equals(strArg) || !(strValue instanceof String) || strValue.hashCode() != hashcode) {
					return false;
				}
				boolean isCmpNE = (ifStrEqualsInsn.getOp() == IfOp.EQ) != ifStrEqualsInsn.getArg(1).isTrue();
				BlockNode thenBlock = isCmpNE ? ifStrEqualsInsn.getElseBlock() : ifStrEqualsInsn.getThenBlock();
				BlockNode elseBlock = isCmpNE ? ifStrEqualsInsn.getThenBlock() : ifStrEqualsInsn.getElseBlock();
				Integer numValue = null;
				if (data.getType() == SwitchStringType.SWITCH_SWITCH || data.getType() == SwitchStringType.IF_SWITCH) {
					InsnNode numInsn = BlockUtils.getLastInsn(getOnlyOneInsnBlock(thenBlock));
					if (thenBlock != null && (numInsn == null || numInsn.getType() == InsnType.SWITCH)) {
						// num is assigned before 1st region. find nearest assign
						BlockNode iDom = thenBlock.getIDom();
						while (iDom != null && numValue == null) {
							for (InsnNode insn : iDom.getInstructions()) {
								numValue = extractConstNumber(data, insn);
							}
							iDom = iDom.getIDom();
						}
						if (numValue == null) {
							return false;
						}
					} else if (numInsn != null && data.getNumArg().sameCodeVar(numInsn.getResult())) {
						numValue = extractConstNumber(data, numInsn);
					} else {
						return false;
					}
				}
				// store str and num assign in switchData
				data.getCases().add(new CaseData((String) strValue, numValue, thenBlock));
				// there may be more string compare (same hashcode)
				BlockNode nextIfBlock = getOnlyOneInsnBlock(elseBlock);
				ifStrEqualsInsn = (IfNode) BlockUtils.getLastInsnWithType(nextIfBlock, InsnType.IF);
			} while (isIfStringEqualsInsn(ifStrEqualsInsn));
		}
		return true;
	}

	/**
	 * SWITCH_SWITCH/IF_SWITCH: create cases according to part2Region (switch), replace keys with strings.
	 * SINGLE_SWITCH: create cases according to part1Region, replace keys with strings.
	 */
	private boolean prepareMergedSwitchCases(SwitchData data) {
		SwitchRegion part1Region = (SwitchRegion) data.getPart1Region();
		SwitchRegion part2Region = data.getPart2Region();
		List<CaseData> cases = data.getCases();
		List<SwitchRegion.CaseInfo> newCases = new ArrayList<>();
		data.setNewCases(newCases);
		if (data.getType() == SwitchStringType.SWITCH_SWITCH || data.getType() == SwitchStringType.IF_SWITCH) {
			// group by num
			Map<Integer, List<Object>> casesMap = new HashMap<>(cases.size());
			for (CaseData caseData : cases) {
				casesMap.computeIfAbsent(caseData.getCodeNum(), v -> new ArrayList<>()).add(caseData.getStrValue());
			}
			SwitchRegion.CaseInfo newDefaultCase = null;
			for (SwitchRegion.CaseInfo caseInfo : Objects.requireNonNull(part2Region).getCases()) {
				SwitchRegion.CaseInfo newCase = new SwitchRegion.CaseInfo(new ArrayList<>(), caseInfo.getContainer());
				for (Object key : caseInfo.getKeys()) {
					Integer intKey = unwrapIntKey(key);
					if (key != SwitchRegion.DEFAULT_CASE_KEY) {
						List<Object> strings = casesMap.remove(Objects.requireNonNull(intKey));
						if (strings == null || strings.isEmpty()) {
							return false;
						}
						newCase.getKeys().addAll(strings);
					} else {
						// last case. add all remaining strings
						newDefaultCase = newCase;
						for (List<Object> strings : casesMap.values()) {
							newCase.getKeys().addAll(strings);
						}
						newCase.getKeys().add(SwitchRegion.DEFAULT_CASE_KEY);
					}
				}
				newCases.add(newCase);
			}
			if (newDefaultCase == null) {
				return false;
			}
		} else if (data.getType() == SwitchStringType.SINGLE_SWITCH){
			// group by block
			Map<BlockNode, List<Object>> casesMap = new HashMap<>(cases.size());
			for (CaseData caseData : cases) {
				casesMap.computeIfAbsent(caseData.getCode(), v -> new ArrayList<>()).add(caseData.getStrValue());
			}
			SwitchInsn swInsn = (SwitchInsn) BlockUtils.getLastInsnWithType(part1Region.getHeader(), InsnType.SWITCH);
			BlockNode defBlock = Objects.requireNonNull(swInsn).getDefTargetBlock();
			if (defBlock != null) {
				casesMap.computeIfAbsent(defBlock, v -> new ArrayList<>()).add(SwitchRegion.DEFAULT_CASE_KEY);
			}
			for (BlockNode code : casesMap.keySet()) {
				IContainer codeRegion = RegionUtils.getBlockContainer(data.getPart1Region(), code);
				if (codeRegion == null) {
					return false;
				}
				newCases.add(new SwitchRegion.CaseInfo(casesMap.get(code), codeRegion));
			}
			// make sure default is the last one
			SwitchRegion.CaseInfo newDefaultCase = ListUtils.filterOnlyOne(newCases,
					info -> info.getKeys().contains(SwitchRegion.DEFAULT_CASE_KEY));
			if (newDefaultCase != null) {
				newCases.remove(newDefaultCase);
				newCases.add(newDefaultCase);
			}
		}
		return true;
	}

	/** replace with new switch. remove original code */
	private static boolean replaceWithMergedSwitch(SwitchData data) {
		MethodNode mth = data.getMth();
		IRegion part1Region = data.getPart1Region();
		IRegion part1Parent = part1Region.getParent();
		SwitchRegion part2Region = data.getPart2Region();
		List<InsnNode> keptInsns = new ArrayList<>();
		BlockNode newHeader;
		if (data.getType() == SwitchStringType.SWITCH_SWITCH || data.getType() == SwitchStringType.SINGLE_SWITCH) {
			newHeader = ((SwitchRegion) part1Region).getHeader();
		} else {
			newHeader = Objects.requireNonNull(part2Region).getHeader();
		}
		// use string arg directly in switch
		InsnNode swInsn = BlockUtils.getLastInsnWithType(newHeader, InsnType.SWITCH);
		InsnNode newSwInsn = Objects.requireNonNull(swInsn).copyWithoutResult();
		newSwInsn.replaceArg(swInsn.getArg(0), data.getStrArg().duplicate());
		BlockUtils.replaceInsn(mth, newHeader, swInsn, newSwInsn);
		keptInsns.add(newSwInsn);

		SwitchRegion replaceRegion = new SwitchRegion(part1Parent, newHeader);
		for (SwitchRegion.CaseInfo caseInfo : data.getNewCases()) {
			IContainer container = caseInfo.getContainer();
			RegionUtils.visitBlocks(mth, container, b -> keptInsns.addAll(b.getInstructions()));
			replaceRegion.addCase(Collections.unmodifiableList(caseInfo.getKeys()), container);
			replaceRegion.updateParent(container, replaceRegion);
		}
		if (!part1Parent.replaceSubBlock(part1Region, replaceRegion)) {
			return false;
		}

		// remove original code
		try {
			List<InsnNode> removeInsns = RegionUtils.collectInsns(mth, part1Region);
			if (part2Region != null) {
				removeInsns.addAll(RegionUtils.collectInsns(mth, part2Region));
				part2Region.getParent().getSubBlocks().remove(part2Region);
			}
			removeInsns.removeAll(keptInsns);
			removeInsns.forEach(i -> i.add(AFlag.REMOVE));
			RegisterArg numArg = data.getNumArg();
			if (numArg != null) {
				for (SSAVar ssaVar : numArg.getSVar().getCodeVar().getSsaVars()) {
					// num value is assigned before 1st region
					InsnNode assignInsn = ssaVar.getAssignInsn();
					if (assignInsn != null) {
						assignInsn.add(AFlag.REMOVE);
					}
					for (RegisterArg useArg : ssaVar.getUseList()) {
						InsnNode parentInsn = useArg.getParentInsn();
						if (parentInsn != null) {
							parentInsn.add(AFlag.REMOVE);
						}
					}
					mth.removeSVar(ssaVar);
				}
			}
			InsnRemover.removeAllMarked(mth);
		} catch (StackOverflowError | Exception e) {
			mth.addWarnComment("Failed to clean up code after switch over string restore", e);
		}
		return true;
	}

	private @Nullable Integer extractConstNumber(SwitchData switchData, @Nullable InsnNode numInsn) {
		if (numInsn == null || numInsn.getArgsCount() != 1) {
			return null;
		}
		Object constVal = InsnUtils.getConstValueByArg(switchData.getMth().root(), numInsn.getArg(0));
		if (constVal instanceof LiteralArg) {
			if (switchData.getNumArg().sameCodeVar(numInsn.getResult())) {
				return (int) ((LiteralArg) constVal).getLiteral();
			}
		}
		return null;
	}

	private Integer unwrapIntKey(Object key) {
		if (key instanceof Integer) {
			return (Integer) key;
		}
		if (key instanceof FieldNode) {
			EncodedValue encodedValue = ((FieldNode) key).get(JadxAttrType.CONSTANT_VALUE);
			if (encodedValue != null && encodedValue.getType() == EncodedType.ENCODED_INT) {
				return (Integer) encodedValue.getValue();
			}
			return null;
		}
		return null;
	}

	private @Nullable RegisterArg getStrHashCodeArg(InsnArg arg) {
		if (arg.isRegister()) {
			return getStrFromInsn(((RegisterArg) arg).getAssignInsn());
		}
		if (arg.isInsnWrap()) {
			return getStrFromInsn(((InsnWrapArg) arg).getWrapInsn());
		}
		return null;
	}

	private @Nullable RegisterArg getStrFromInsn(@Nullable InsnNode insn) {
		if (insn == null || insn.getType() != InsnType.INVOKE) {
			return null;
		}
		InvokeNode invInsn = (InvokeNode) insn;
		MethodInfo callMth = invInsn.getCallMth();
		if (!callMth.getRawFullId().equals("java.lang.String.hashCode()I")) {
			return null;
		}
		InsnArg arg = invInsn.getInstanceArg();
		if (arg == null || !arg.isRegister()) {
			return null;
		}
		return (RegisterArg) arg;
	}

	private static boolean isIfStringEqualsInsn(InsnNode ifInsn) {
		if (ifInsn != null && ifInsn.getType() == InsnType.IF && ifInsn.getArgsCount() == 2) {
			InsnNode wrapped = InsnUtils.getWrappedInsn(ifInsn.getArg(0));
			return wrapped != null && wrapped.getType() == InsnType.INVOKE
					&& ((InvokeNode) wrapped).getCallMth().getRawFullId().equals("java.lang.String.equals(Ljava/lang/Object;)Z");
		}
		return false;
	}

	private static @Nullable BlockNode getOnlyOneInsnBlock(BlockNode b) {
		while (b != null) {
			int size = b.getInstructions().size();
			if (size == 0) {
				b = BlockUtils.getNextBlock(b);
				continue;
			}
			return size == 1 ? b : null;
		}
		return null;
	}

	private static final class SwitchData {
		private final MethodNode mth;
		private SwitchStringType type = SwitchStringType.SWITCH_SWITCH;
		// first switch/if region
		private final IRegion part1Region;
		// second switch region, null if SINGLE_SWITCH
		private @Nullable SwitchRegion part2Region;
		// each case is a str in part1Region, with its num or code block
		private List<CaseData> cases;
		private List<SwitchRegion.CaseInfo> newCases;
		private RegisterArg numArg;
		private RegisterArg strArg;

		private SwitchData(MethodNode mth, IRegion part1Region) {
			this.mth = mth;
			this.part1Region = part1Region;
		}

		public SwitchStringType getType() {
			return type;
		}

		public void setType(SwitchStringType type) {
			this.type = type;
		}

		public List<CaseData> getCases() {
			return cases;
		}

		public void setCases(List<CaseData> cases) {
			this.cases = cases;
		}

		public List<SwitchRegion.CaseInfo> getNewCases() {
			return newCases;
		}

		public void setNewCases(List<SwitchRegion.CaseInfo> cases) {
			this.newCases = cases;
		}

		public MethodNode getMth() {
			return mth;
		}

		public IRegion getPart1Region() {
			return part1Region;
		}

		public @Nullable SwitchRegion getPart2Region() {
			return part2Region;
		}

		public void setPart2Region(@Nullable SwitchRegion part2Region) {
			this.part2Region = part2Region;
		}

		public RegisterArg getNumArg() {
			return numArg;
		}

		public void setNumArg(RegisterArg numArg) {
			this.numArg = numArg;
		}

		public RegisterArg getStrArg() {
			return strArg;
		}

		public void setStrArg(RegisterArg strArg) {
			this.strArg = strArg;
		}
	}

	private static final class CaseData {
		private final String strValue;
		private final BlockNode code;
		private final Integer codeNum;

		private CaseData(String strValue, Integer codeNum, BlockNode code) {
			this.strValue = strValue;
			this.code = code;
			this.codeNum = codeNum;
		}

		public String getStrValue() {
			return strValue;
		}

		public @Nullable BlockNode getCode() {
			return code;
		}

		public Integer getCodeNum() {
			return codeNum;
		}

		@Override
		public String toString() {
			return "CaseData{" + strValue + '}';
		}
	}

	private enum SwitchStringType {
		SINGLE_SWITCH,
		IF_SWITCH,
		SWITCH_SWITCH
	}
}
