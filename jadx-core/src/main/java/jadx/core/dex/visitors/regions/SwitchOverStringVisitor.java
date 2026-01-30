package jadx.core.dex.visitors.regions;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;

import org.jetbrains.annotations.Nullable;

import jadx.api.plugins.input.data.annotations.EncodedType;
import jadx.api.plugins.input.data.annotations.EncodedValue;
import jadx.api.plugins.input.data.attributes.JadxAttrType;
import jadx.core.dex.attributes.AFlag;
import jadx.core.dex.attributes.AType;
import jadx.core.dex.attributes.IAttributeNode;
import jadx.core.dex.attributes.nodes.CodeFeaturesAttr;
import jadx.core.dex.attributes.nodes.CodeFeaturesAttr.CodeFeature;
import jadx.core.dex.attributes.nodes.SwitchStringAttr;
import jadx.core.dex.info.MethodInfo;
import jadx.core.dex.instructions.IfNode;
import jadx.core.dex.instructions.IfOp;
import jadx.core.dex.instructions.InsnType;
import jadx.core.dex.instructions.InvokeNode;
import jadx.core.dex.instructions.PhiInsn;
import jadx.core.dex.instructions.SwitchInsn;
import jadx.core.dex.instructions.args.InsnArg;
import jadx.core.dex.instructions.args.InsnWrapArg;
import jadx.core.dex.instructions.args.LiteralArg;
import jadx.core.dex.instructions.args.RegisterArg;
import jadx.core.dex.instructions.args.SSAVar;
import jadx.core.dex.nodes.BlockNode;
import jadx.core.dex.nodes.FieldNode;
import jadx.core.dex.nodes.IBranchRegion;
import jadx.core.dex.nodes.IContainer;
import jadx.core.dex.nodes.IRegion;
import jadx.core.dex.nodes.InsnNode;
import jadx.core.dex.nodes.MethodNode;
import jadx.core.dex.regions.SwitchRegion;
import jadx.core.dex.regions.conditions.Compare;
import jadx.core.dex.regions.conditions.IfCondition;
import jadx.core.dex.regions.conditions.IfInfo;
import jadx.core.dex.regions.conditions.IfRegion;
import jadx.core.dex.visitors.AbstractVisitor;
import jadx.core.dex.visitors.JadxVisitor;
import jadx.core.utils.BlockUtils;
import jadx.core.utils.InsnRemover;
import jadx.core.utils.InsnUtils;
import jadx.core.utils.RegionUtils;
import jadx.core.utils.Utils;
import jadx.core.utils.exceptions.JadxException;

@JadxVisitor(
		name = "SwitchOverStringVisitor",
		desc = "Restore switch over string",
		runAfter = IfRegionVisitor.class,
		runBefore = ReturnVisitor.class
)
public class SwitchOverStringVisitor extends AbstractVisitor implements IRegionIterativeVisitor {

	@Override
	public void visit(MethodNode mth) throws JadxException {
		if (!CodeFeaturesAttr.contains(mth, CodeFeature.SWITCH)) {
			return;
		}
		DepthRegionTraversal.traverseIterative(mth, this);
	}

	@Override
	public boolean visitRegion(MethodNode mth, IRegion region) {
		// d8 optimization could turn first switch into if
		if (region instanceof SwitchRegion || region instanceof IfRegion) {
			return restoreSwitchOverString(mth, (IBranchRegion) region);
		}
		return false;
	}

	private boolean restoreSwitchOverString(MethodNode mth, IBranchRegion hashSwitch) {
		try {
			// second switch
			IContainer nextContainer = RegionUtils.getNextContainer(mth, hashSwitch);
			if (!(nextContainer instanceof SwitchRegion)) {
				return false;
			}
			SwitchRegion codeSwitch = (SwitchRegion) nextContainer;
			InsnNode codeSwInsn = BlockUtils.getLastInsnWithType(codeSwitch.getHeader(), InsnType.SWITCH);
			RegisterArg numArg = getNumArgOf2ndSwitch(codeSwitch.getHeader());
			if (codeSwInsn == null || numArg == null) {
				return false;
			}

			RegisterArg strArg;
			SwitchData switchData;
			if (hashSwitch instanceof SwitchRegion) {
				SwitchRegion hashSwitch2 = (SwitchRegion) hashSwitch;
				InsnNode hashSwInsn = BlockUtils.getLastInsnWithType(hashSwitch2.getHeader(), InsnType.SWITCH);
				if (hashSwInsn == null) {
					return false;
				}
				strArg = getStrHashCodeArg(hashSwInsn.getArg(0));
				if (strArg == null) {
					return false;
				}
				int casesCount = hashSwitch2.getCases().size();
				boolean defaultCaseAdded = hashSwitch2.getCases().stream().anyMatch(SwitchRegion.CaseInfo::isDefaultCase);
				int casesWithString = defaultCaseAdded ? casesCount - 1 : casesCount;
				SSAVar strVar = strArg.getSVar();
				if (strVar.getUseCount() - 1 < casesWithString) {
					// one 'hashCode' invoke and at least one 'equals' per case
					return false;
				}
				// quick checks done, start collecting data to create a new switch region
				Map<InsnNode, String> strEqInsns = collectEqualsInsns(mth, strVar);
				if (strEqInsns.size() < casesWithString) {
					return false;
				}
				switchData = new SwitchData(mth, hashSwitch);
				switchData.setNumArg(numArg);
				switchData.setStrEqInsns(strEqInsns);
				switchData.setCases(new ArrayList<>(casesCount));
				SwitchStringAttr attr = new SwitchStringAttr(codeSwitch.getHeader());
				// TODO `processor.collectMergeData` replace `processCase`.
				// what about case without break?
//				FirstStageProcessor processor = new FirstStageSwitchProcessor();
				for (SwitchRegion.CaseInfo swCaseInfo : hashSwitch2.getCases()) {
					if (!processCase(mth, switchData, attr, swCaseInfo)) {
						mth.addWarnComment("Failed to restore switch over string. Please report as a decompilation issue");
						return false;
					}
				}
			} else if (hashSwitch instanceof IfRegion) {
				SwitchStringAttr attr = codeSwitch.getHeader().get(AType.SWITCH_STRING);
				if (attr == null) {
					return false;
				}
				IfRegion hashSwitch2 = (IfRegion) hashSwitch;
				strArg = attr.getTargetStrArg();
				SSAVar strVar = strArg.getSVar();
				Map<InsnNode, String> strEqInsns = collectEqualsInsns(mth, strVar);
				List<SwitchStringAttr.Case> attrCases = attr.getAllCases();

				switchData = new SwitchData(mth, hashSwitch);
				switchData.setNumArg(numArg);
				switchData.setStrEqInsns(strEqInsns);
				switchData.setCases(new ArrayList<>(attrCases.size()));
				RegionUtils.visitBlockNodes(mth, hashSwitch2,
						block -> switchData.getToRemove().addAll(block.getInstructions()));
				for (SwitchStringAttr.Case caseInfo : attrCases) {
					CaseData caseData = new CaseData();
					caseData.setCodeNum(caseInfo.getNumKeyIn2ndSwitch());
					caseData.getStrValues().addAll(caseInfo.getStrs());
					switchData.getCases().add(caseData);
				}
			} else {
				return false;
			}
			// match remapping var to collect code from second switch
			if (!mergeWithCode(switchData, codeSwitch)) {
				mth.addWarnComment("Failed to restore switch over string. Please report as a decompilation issue");
				return false;
			}
			// all checks passed, replace with new switch
			IRegion parentRegion = codeSwitch.getParent();
			SwitchRegion replaceRegion = new SwitchRegion(parentRegion, codeSwitch.getHeader());
			for (SwitchRegion.CaseInfo caseInfo : switchData.getNewCases()) {
				replaceRegion.addCase(Collections.unmodifiableList(caseInfo.getKeys()), caseInfo.getContainer());
			}
			if (!parentRegion.replaceSubBlock(codeSwitch, replaceRegion)) {
				mth.addWarnComment("Failed to restore switch over string. Please report as a decompilation issue");
				return false;
			}
			// replace confirmed, remove original code
			markCodeForRemoval(switchData);
			// use string arg directly in switch
			codeSwInsn.replaceArg(numArg, strArg.duplicate());
			codeSwitch.getHeader().remove(AType.SWITCH_STRING);
			return true;
		} catch (StackOverflowError | Exception e) {
			mth.addWarnComment("Failed to restore switch over string. Please report as a decompilation issue", e);
			return false;
		}
	}

	private static void markCodeForRemoval(SwitchData switchData) {
		MethodNode mth = switchData.getMth();
		try {
			switchData.getToRemove().forEach(i -> i.add(AFlag.REMOVE));
			IBranchRegion hashSwitch = switchData.getHashSwitch();
			hashSwitch.getParent().getSubBlocks().remove(hashSwitch);
			if (hashSwitch instanceof SwitchRegion) {
				((SwitchRegion) hashSwitch).getHeader().add(AFlag.REMOVE);
			}
			RegisterArg numArg = switchData.getNumArg();
			if (numArg != null) {
				for (SSAVar ssaVar : numArg.getSVar().getCodeVar().getSsaVars()) {
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
			// TODO currently cannot delete `int i = str.hashCode()` otherwise error.
			// keep second switch header, which used as replaced switchRegion header
			for (InsnNode secondHeader : switchData.getCodeSwitch().getHeader().getInstructions()) {
				secondHeader.remove(AFlag.REMOVE);
			}
			InsnRemover.removeAllMarked(mth);
		} catch (StackOverflowError | Exception e) {
			mth.addWarnComment("Failed to clean up code after switch over string restore", e);
		}
	}

	private boolean mergeWithCode(SwitchData switchData, SwitchRegion codeSwitch) {
		List<CaseData> cases = switchData.getCases();

		// TODO: additional checks for found index numbers
		cases.sort(Comparator.comparingInt(CaseData::getCodeNum));

		// extract complete
		Map<Integer, CaseData> casesMap = new HashMap<>(cases.size());
		for (CaseData caseData : cases) {
			CaseData prev = casesMap.put(caseData.getCodeNum(), caseData);
			if (prev != null) {
				return false;
			}
			RegionUtils.visitBlocks(switchData.getMth(), caseData.getCode(),
					block -> switchData.getToRemove().add(block));
		}

		List<SwitchRegion.CaseInfo> newCases = new ArrayList<>();
		for (SwitchRegion.CaseInfo caseInfo : codeSwitch.getCases()) {
			SwitchRegion.CaseInfo newCase = null;
			for (Object key : caseInfo.getKeys()) {
				Integer intKey = unwrapIntKey(key);
				if (intKey != null) {
					CaseData caseData = casesMap.remove(intKey);
					if (caseData == null) {
						return false;
					}
					if (newCase == null) {
						List<Object> keys = new ArrayList<>(caseData.getStrValues());
						newCase = new SwitchRegion.CaseInfo(keys, caseInfo.getContainer());
					} else {
						// merge cases
						newCase.getKeys().addAll(caseData.getStrValues());
					}
				} else if (key == SwitchRegion.DEFAULT_CASE_KEY) {
					var iterator = casesMap.entrySet().iterator();
					while (iterator.hasNext()) {
						CaseData caseData = iterator.next().getValue();
						if (newCase == null) {
							List<Object> keys = new ArrayList<>(caseData.getStrValues());
							newCase = new SwitchRegion.CaseInfo(keys, caseInfo.getContainer());
						} else {
							// merge cases
							newCase.getKeys().addAll(caseData.getStrValues());
						}
						iterator.remove();
					}
					if (newCase == null) {
						newCase = new SwitchRegion.CaseInfo(new ArrayList<>(), caseInfo.getContainer());
					}
					newCase.getKeys().add(SwitchRegion.DEFAULT_CASE_KEY);
				} else {
					return false;
				}
			}
			newCases.add(newCase);
		}
		switchData.setCodeSwitch(codeSwitch);
		switchData.setNewCases(newCases);
		return true;
	}

	private static @Nullable Integer extractConstNumber(MethodNode mth, @Nullable InsnNode numInsn, RegisterArg numArg) {
		if (numInsn == null || numInsn.getArgsCount() != 1) {
			return null;
		}
		Object constVal = InsnUtils.getConstValueByArg(mth.root(), numInsn.getArg(0));
		if (constVal instanceof LiteralArg) {
			if (numArg.sameCodeVar(numInsn.getResult())) {
				return (int) ((LiteralArg) constVal).getLiteral();
			}
		}
		return null;
	}

	private static @Nullable InsnNode searchConstInsn(SwitchData switchData, CaseData caseData, InsnArg numArg) {
		IContainer container = caseData.getCode();
		if (container != null) {
			List<InsnNode> insns = RegionUtils.collectInsns(switchData.getMth(), container);
			insns.removeIf(i -> i.getType() == InsnType.BREAK);
			if (insns.size() == 1) {
				return insns.get(0);
			}
		} else if (caseData.getBlockRef() != null) {
			// variable used unchanged on path from block ref
			BlockNode blockRef = caseData.getBlockRef();
			if (numArg.isRegister()) {
				InsnNode assignInsn = ((RegisterArg) numArg).getSVar().getAssignInsn();
				if (assignInsn != null && assignInsn.getType() == InsnType.PHI) {
					RegisterArg arg = ((PhiInsn) assignInsn).getArgByBlock(blockRef);
					if (arg != null) {
						return arg.getAssignInsn();
					}
				}
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

	private static Map<InsnNode, String> collectEqualsInsns(MethodNode mth, SSAVar strVar) {
		Map<InsnNode, String> map = new IdentityHashMap<>(strVar.getUseCount() - 1);
		for (RegisterArg useReg : strVar.getUseList()) {
			InsnNode parentInsn = useReg.getParentInsn();
			if (parentInsn != null && parentInsn.getType() == InsnType.INVOKE) {
				InvokeNode inv = (InvokeNode) parentInsn;
				if (inv.getCallMth().getRawFullId().equals("java.lang.String.equals(Ljava/lang/Object;)Z")) {
					InsnArg strArg = inv.getArg(1);
					Object strValue = InsnUtils.getConstValueByArg(mth.root(), strArg);
					if (strValue instanceof String) {
						map.put(parentInsn, (String) strValue);
					}
				}
			}
		}
		return map;
	}

	private boolean readCodeNum(SwitchData switchData) {
		RegisterArg numArg = switchData.getNumArg();
		List<CaseData> cases = switchData.getCases();
		// search index assign in cases code
		int extracted = 0;
		for (CaseData caseData : cases) {
			InsnNode numInsn = searchConstInsn(switchData, caseData, numArg);
			Integer num = extractConstNumber(switchData.getMth(), numInsn, numArg);
			if (num != null) {
				caseData.setCodeNum(num);
				extracted++;
			}
		}
		if (extracted == 0) {
			// nothing to merge, code already inside first switch cases
			return true;
		}
		return extracted == cases.size();
	}

	private boolean processCase(MethodNode mth, SwitchData switchData, SwitchStringAttr attr, SwitchRegion.CaseInfo caseInfo) {
		if (caseInfo.isDefaultCase()) {
			CaseData caseData = new CaseData();
			caseData.setCode(caseInfo.getContainer());
			return true;
		}
		AtomicBoolean fail = new AtomicBoolean(false);
		RegionUtils.visitRegions(mth, caseInfo.getContainer(), region -> {
			if (fail.get()) {
				return false;
			}
			if (region instanceof IfRegion) {
				CaseData caseData = fillCaseData((IfRegion) region, switchData, attr);
				if (caseData == null) {
					fail.set(true);
					return false;
				}
				switchData.getCases().add(caseData);
			}
			return true;
		});
		return !fail.get();
	}

	private @Nullable CaseData fillCaseData(IfRegion ifRegion, SwitchData switchData, SwitchStringAttr attr) {
		IfCondition condition = Objects.requireNonNull(ifRegion.getCondition());
		boolean neg = false;
		if (condition.getMode() == IfCondition.Mode.NOT) {
			condition = condition.getArgs().get(0);
			neg = true;
		}
		Compare compare = condition.getCompare();
		if (compare == null) {
			return null;
		}
		IfNode ifInsn = compare.getInsn();
		InsnArg firstArg = ifInsn.getArg(0);
		String str = null;
		if (firstArg.isInsnWrap()) {
			str = switchData.getStrEqInsns().get(((InsnWrapArg) firstArg).getWrapInsn());
		}
		if (str == null) {
			return null;
		}
		if (ifInsn.getOp() == IfOp.NE && ifInsn.getArg(1).isTrue()) {
			neg = true;
		}
		if (ifInsn.getOp() == IfOp.EQ && ifInsn.getArg(1).isFalse()) {
			neg = true;
		}
		switchData.getToRemove().add(ifInsn);
		switchData.getToRemove().addAll(ifRegion.getConditionBlocks());

		CaseData caseData = new CaseData();
		caseData.getStrValues().add(str);

		IContainer codeContainer = neg ? ifRegion.getElseRegion() : ifRegion.getThenRegion();
		if (codeContainer == null) {
			// no code
			// use last condition block for later data tracing
			caseData.setBlockRef(Utils.last(ifRegion.getConditionBlocks()));
		} else {
			caseData.setCode(codeContainer);
		}
		RegisterArg numArg = switchData.getNumArg();
		InsnNode numInsn = searchConstInsn(switchData, caseData, numArg);
		Integer num = extractConstNumber(switchData.getMth(), numInsn, numArg);
		if (num == null) {
			return null;
		}
		caseData.setCodeNum(num);
		return caseData;
	}

	private static @Nullable RegisterArg getStrHashCodeArg(InsnArg arg) {
		if (arg.isRegister()) {
			return getStrFromInsn(((RegisterArg) arg).getAssignInsn());
		}
		if (arg.isInsnWrap()) {
			return getStrFromInsn(((InsnWrapArg) arg).getWrapInsn());
		}
		return null;
	}

	private static @Nullable RegisterArg getStrFromInsn(@Nullable InsnNode insn) {
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

	private static IfCondition unwrapNOT2Compare(IfCondition c) {
		if (c != null && c.getMode() == IfCondition.Mode.COMPARE) {
			return c;
		} else if (c != null && c.getMode() == IfCondition.Mode.NOT) {
			c = c.getArgs().get(0);
			return unwrapNOT2Compare(c);
		} else {
			return null;
		}
	}

	/** get numArg in second switch header */
	private static @Nullable RegisterArg getNumArgOf2ndSwitch(BlockNode switchBlock) {
		InsnNode insn = BlockUtils.getLastInsnWithType(switchBlock, InsnType.SWITCH);
		return insn == null ? null : Utils.cast(insn.getArg(0), RegisterArg.class);
	}

	public static void preProcessSwitchStringFirstIf(IfInfo currentIf) {
		MethodNode mth = currentIf.getMth();
		IfCondition condition = unwrapNOT2Compare(currentIf.getCondition());
		if (condition == null) {
			return;
		}
		IfNode hashIfInsn = condition.getCompare().getInsn();
		BlockNode secondSwitchBlock = BlockUtils.getPathCross(mth, hashIfInsn.getThenBlock(), hashIfInsn.getElseBlock());
		if (secondSwitchBlock == null || secondSwitchBlock.get(AType.SWITCH_STRING) != null) {
			return;
		}

		SwitchStringAttr attr = new SwitchStringAttr(secondSwitchBlock);
		FirstStageProcessor processor = new FirstStageIfProcessor();
		if (processor.initArg(hashIfInsn, attr)
				&& processor.collectMergeData(mth, hashIfInsn, attr)) {
			secondSwitchBlock.addAttr(attr);
		}
	}

	private static final class SwitchData {
		private final MethodNode mth;
		private final IBranchRegion hashSwitch;
		private final List<IAttributeNode> toRemove = new ArrayList<>();
		private Map<InsnNode, String> strEqInsns;
		private List<CaseData> cases;
		private List<SwitchRegion.CaseInfo> newCases;
		private SwitchRegion codeSwitch;
		private RegisterArg numArg;

		private SwitchData(MethodNode mth, IBranchRegion hashSwitch) {
			this.mth = mth;
			this.hashSwitch = hashSwitch;
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

		public Map<InsnNode, String> getStrEqInsns() {
			return strEqInsns;
		}

		public void setStrEqInsns(Map<InsnNode, String> strEqInsns) {
			this.strEqInsns = strEqInsns;
		}

		public IBranchRegion getHashSwitch() {
			return hashSwitch;
		}

		public List<IAttributeNode> getToRemove() {
			return toRemove;
		}

		public SwitchRegion getCodeSwitch() {
			return codeSwitch;
		}

		public void setCodeSwitch(SwitchRegion codeSwitch) {
			this.codeSwitch = codeSwitch;
		}

		public RegisterArg getNumArg() {
			return numArg;
		}

		public void setNumArg(RegisterArg numArg) {
			this.numArg = numArg;
		}
	}

	private static final class CaseData {
		private final List<String> strValues = new ArrayList<>();
		private @Nullable IContainer code = null;
		private @Nullable BlockNode blockRef = null;
		private int codeNum = -1;

		public List<String> getStrValues() {
			return strValues;
		}

		public @Nullable IContainer getCode() {
			return code;
		}

		public void setCode(@Nullable IContainer code) {
			this.code = code;
		}

		public @Nullable BlockNode getBlockRef() {
			return blockRef;
		}

		public void setBlockRef(@Nullable BlockNode blockRef) {
			this.blockRef = blockRef;
		}

		public int getCodeNum() {
			return codeNum;
		}

		public void setCodeNum(int codeNum) {
			this.codeNum = codeNum;
		}

		@Override
		public String toString() {
			return "CaseData{" + strValues + '}';
		}
	}

	/** process the first stage (switch or if), where strings are compared and numbers are assigned */
	private abstract static class FirstStageProcessor {

		/**
		 * collect const strings to be merged to 2nd switch, and corresponding numbers. and some other data.
		 * return false if it is not a switch over string.
		 */
		public boolean collectMergeData(MethodNode mth, InsnNode startInsn, SwitchStringAttr attr) {
			return collectHashCodes(startInsn, attr) && collectConstStrAndNums(mth, attr);
		}

		// TODO init numArg， strArg, strhashcodearg,
		public boolean initArg(InsnNode startInsn, SwitchStringAttr attr) {
			return true;
		}

		/** traverse 1st if cases to collect str compare containers, targetStrHashArg and targetStrArg. */
		protected abstract boolean collectHashCodes(InsnNode startInsn, SwitchStringAttr attr);

		/** traverse all str.equals() insns, collect const strings and their nums in 2nd switch. */
		protected abstract boolean collectConstStrAndNums(MethodNode mth, SwitchStringAttr attr);

		/** extract insn 'str.equals("aa")' from ifInsn e.g. 'if (str.equals("aa") == true)'. */
		protected static @Nullable InvokeNode getStrEqInvokeFromIfInsn(IfNode strIfInsn) {
			if (strIfInsn.getOp() != IfOp.EQ && strIfInsn.getOp() != IfOp.NE
					|| !strIfInsn.getArg(0).isInsnWrap()) {
				return null;
			}
			InsnWrapArg strCmpArg = (InsnWrapArg) strIfInsn.getArg(0);
			InvokeNode eqIvkInsn = Utils.cast(strCmpArg.getWrapInsn(), InvokeNode.class);
			if (eqIvkInsn == null || !eqIvkInsn.getCallMth().getRawFullId().equals("java.lang.String.equals(Ljava/lang/Object;)Z")) {
				eqIvkInsn = null;
			}
			return eqIvkInsn;
		}

		protected static @Nullable BlockNode getBranchBlockSkipEmpty(IfNode ifInsn, boolean then) {
			BlockNode b = then ? ifInsn.getThenBlock() : ifInsn.getElseBlock();
			if (b != null && b.getInstructions().isEmpty()) {
				b = getNextBlockSkipEmpty(b);
			}
			return b;
		}

		/** get first next block which insns is not empty. */
		protected static @Nullable BlockNode getNextBlockSkipEmpty(BlockNode b) {
			if (b == null || b.isMthExitBlock()) {
				return null;
			}
			while (true) {
				b = BlockUtils.getNextBlock(b);
				if (b == null || b.isMthExitBlock()) {
					return null;
				}
				if (!b.getInstructions().isEmpty()) {
					return b;
				}
			}
		}
	}

	private static final class FirstStageIfProcessor extends FirstStageProcessor {

		@Override
		protected boolean collectHashCodes(InsnNode startInsn, SwitchStringAttr attr) {
			IfNode hashIfInsn = Utils.cast(startInsn, IfNode.class);
			if (hashIfInsn == null) {
				return false;
			}
			RegisterArg targetStrHashArg = null;
			RegisterArg targetStrArg = null;
			Map<Object, BlockNode> strCompareMap = attr.getStrCompareMap();
			Set<InsnNode> visited = new HashSet<>();
			while (true) {
				if (!visited.add(hashIfInsn)) {
					return false;
				}
				// 1st arg is targetStr hashCode, 2nd arg is keyStr hashcode
				RegisterArg currTargetStrHashArg = Utils.cast(hashIfInsn.getArg(0), RegisterArg.class);
				LiteralArg currKeyStrHashArg = Utils.cast(hashIfInsn.getArg(1), LiteralArg.class);
				if (currTargetStrHashArg == null || currKeyStrHashArg == null) {
					return false;
				}
				if (targetStrHashArg == null) {
					targetStrHashArg = currTargetStrHashArg;
					targetStrArg = getStrHashCodeArg(targetStrHashArg);
					if (targetStrArg == null) {
						return false;
					}
				} else if (!targetStrHashArg.equals(currTargetStrHashArg)) {
					return false;
				}

				boolean neg = hashIfInsn.getOp() == IfOp.NE;
				// eqHash -> if (str.equals()), neHash -> next hashcode case
				BlockNode eqHashBranch = getBranchBlockSkipEmpty(hashIfInsn, !neg);
				BlockNode neHashBranch = getBranchBlockSkipEmpty(hashIfInsn, neg);
				if (eqHashBranch == null || neHashBranch == null) {
					return false;
				}
				// collect str.equals() blocks. process them afterwards.
				int keyStrHash = (int) currKeyStrHashArg.getLiteral();
				strCompareMap.put(keyStrHash, eqHashBranch);

				InsnNode afterHashInsn = neHashBranch.getInstructions().get(0);
				// next hashcode case
				if (afterHashInsn instanceof IfNode) {
					hashIfInsn = (IfNode) afterHashInsn;
					continue;
				}
				// default case
				if (afterHashInsn.getType() == InsnType.CONST) {
					strCompareMap.put(SwitchRegion.DEFAULT_CASE_KEY, neHashBranch);
					neHashBranch = getNextBlockSkipEmpty(neHashBranch);
					if (neHashBranch == null) {
						return false;
					}
					afterHashInsn = neHashBranch.getInstructions().get(0);
				}
				// 1st if end. next is 2nd switch
				if (afterHashInsn instanceof SwitchInsn) {
					if (attr.getCodeSwitchBlock() != neHashBranch) {
						return false;
					}
					break;
				} else {
					return false;
				}
			}
			attr.setTargetStrArg(targetStrArg);
			attr.setTargetStrHashArg(targetStrHashArg);
			return true;
		}

		@Override
		protected boolean collectConstStrAndNums(MethodNode mth, SwitchStringAttr attr) {
			BlockNode secondSwitchBlock = attr.getCodeSwitchBlock();
			RegisterArg numArg = getNumArgOf2ndSwitch(secondSwitchBlock);
			for (Map.Entry<Object, BlockNode> entry : attr.getStrCompareMap().entrySet()) {
				// default case
				if (entry.getKey() == SwitchRegion.DEFAULT_CASE_KEY) {
					BlockNode defaultBranch = entry.getValue();
					// ensure next is 2nd switch
					if (getNextBlockSkipEmpty(defaultBranch) != secondSwitchBlock) {
						return false;
					}
					InsnNode assignIndexInsn = defaultBranch.getInstructions().get(0);
					Integer num = extractConstNumber(mth, assignIndexInsn, numArg);
					if (num == null) {
						return false;
					}
					attr.getCaseByNum(num).addStr(null);
					continue;
				}

				int strHash = (Integer) entry.getKey();
				BlockNode strCompareBlock = entry.getValue();
				IfNode strIfInsn = Utils.cast(strCompareBlock.getInstructions().get(0), IfNode.class);
				boolean neg;
				if (strIfInsn != null && strIfInsn.getOp() == IfOp.EQ) {
					neg = false;
				} else if (strIfInsn != null && strIfInsn.getOp() == IfOp.NE) {
					neg = true;
				} else {
					return false;
				}
				if (strIfInsn.getArg(1).isFalse()) {
					neg = !neg;
				}

				BlockNode eqStrBranch = getBranchBlockSkipEmpty(strIfInsn, !neg);
				BlockNode neStrBranch = getBranchBlockSkipEmpty(strIfInsn, neg);
				if (eqStrBranch == null || neStrBranch == null
						|| getNextBlockSkipEmpty(eqStrBranch) != secondSwitchBlock) {
					return false;
				}

				IfNode currStrIf = strIfInsn;
				Set<InsnNode> visited = new HashSet<>();
				while (true) {
					InvokeNode eqIvkInsn = getStrEqInvokeFromIfInsn(currStrIf);
					if (eqIvkInsn == null || !visited.add(eqIvkInsn)) {
						return false;
					}
					Object strValue = InsnUtils.getConstValueByArg(mth.root(), eqIvkInsn.getArg(1));
					if (!attr.getTargetStrArg().equals(eqIvkInsn.getInstanceArg())
							|| !(strValue instanceof String) || strValue.hashCode() != strHash) {
						return false;
					}

					// save const string and its num in 2nd switch
					InsnNode assignIndexInsn = eqStrBranch.getInstructions().get(0);
					Integer num = extractConstNumber(mth, assignIndexInsn, numArg);
					if (num == null) {
						return false;
					}
					attr.getCaseByNum(num).addStr((String) strValue);

					InsnNode neStrBranchInsn = neStrBranch.getInstructions().get(0);
					if (neStrBranchInsn instanceof IfNode) {
						// next constStr compare. (string is different but hashcode is same)
						currStrIf = (IfNode) neStrBranchInsn;
					} else if (neStrBranchInsn.getType() == InsnType.CONST) {
						// default case. ensure next is 2nd switch
						if (getNextBlockSkipEmpty(neStrBranch) != secondSwitchBlock) {
							return false;
						}
						break;
					} else {
						return false;
					}
				}
			}
			return true;
		}
	}

	private static final class FirstStageSwitchProcessor extends FirstStageProcessor {
		private final SwitchRegion hashSwitch;

		public FirstStageSwitchProcessor(SwitchRegion hashSwitch) {
			this.hashSwitch = hashSwitch;
		}

		@Override
		protected boolean collectHashCodes(InsnNode startInsn, SwitchStringAttr attr) {
			SwitchInsn swInsn = Utils.cast(startInsn, SwitchInsn.class);
			if (swInsn == null) {
				return false;
			}

			return true;
		}

		@Override
		protected boolean collectConstStrAndNums(MethodNode mth, SwitchStringAttr attr) {
			return false;
		}
	}
}
