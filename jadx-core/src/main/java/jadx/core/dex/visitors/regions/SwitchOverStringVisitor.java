package jadx.core.dex.visitors.regions;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
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
import jadx.core.dex.regions.conditions.IfRegion;
import jadx.core.dex.visitors.AbstractVisitor;
import jadx.core.dex.visitors.JadxVisitor;
import jadx.core.utils.BlockUtils;
import jadx.core.utils.InsnRemover;
import jadx.core.utils.InsnUtils;
import jadx.core.utils.RegionUtils;
import jadx.core.utils.Utils;
import jadx.core.utils.exceptions.JadxException;
import jadx.core.utils.exceptions.JadxRuntimeException;

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
			if (codeSwInsn == null || !codeSwInsn.getArg(0).isRegister()) {
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
				List<SwitchRegion.CaseInfo> hashCases = hashSwitch2.getCases();
				int casesCount = hashCases.size();
				boolean defaultCaseAdded = hashCases.stream().anyMatch(SwitchRegion.CaseInfo::isDefaultCase);
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
				switchData.setNumArg((RegisterArg) codeSwInsn.getArg(0));
				switchData.setStrEqInsns(strEqInsns);
				switchData.setCases(new ArrayList<>(casesCount));
				for (SwitchRegion.CaseInfo swCaseInfo : hashCases) {
					if (!processCase(switchData, swCaseInfo)) {
						mth.addWarnComment("Failed to restore switch over string. Please report as a decompilation issue");
						return false;
					}
				}
				if (!setCodeNum(switchData)) {
					return false;
				}
			} else if (hashSwitch instanceof IfRegion) {
//				{
//					List<SwitchRegion.CaseInfo> hashCases = new ArrayList<>();
//					IfRegion hashSwitch2 = (IfRegion) hashSwitch;
//					SplitConditions splitConditions = new SplitConditions();
//					splitCondition(splitConditions, hashSwitch2.getCondition());
//					if (!splitConditions.isValid()) {
//						return false;
//					}
//					// 外层 if, 判断 hashcode。但也可能包含了判断 str.equals() 的 condition
//					for (IfCondition condition : splitConditions.list) {
//						Compare compare = condition.getCompare();
//						if (compare == null || compare.getInsn().getArgsCount() != 2) {
//							return false;
//						}
//						IfNode ifInsn = compare.getInsn();
//						// first arg is the value of str.hashCode(), second arg is hashcode of string case key
//						InsnArg firstArg = ifInsn.getArg(0);
//						if (!(firstArg instanceof RegisterArg)) {
//							return false;
//						}
//						// 目标字符串的 hashcode, 用于和已知的 hashcode 比较
//						SSAVar hashVar = ((RegisterArg) firstArg).getSVar();
//						strArg = getStrFromInsn(hashVar.getAssignInsn());
//						if (strArg == null) {
//							return false;
//						}
//
//						List<BlockNode> regionSubBlockNodes = new ArrayList<>();
//						RegionUtils.visitBlockNodes(mth, hashSwitch2, regionSubBlockNodes::add);
//
//						// 外层 if，hashcode 对比
//						for (RegisterArg useArg : hashVar.getUseList()) {
//							InsnNode useInsn = useArg.getParentInsn();
//							if (!(useInsn instanceof IfNode) || useInsn.getArgsCount() != 2) {
//								return false;
//							}
//							IfNode useInsn2 = (IfNode) useInsn;
//							int key = (int) ((LiteralArg) useInsn2.getArg(1)).getLiteral();
//
//							BlockNode hashEqBlock = BlockUtils.getBlockByInsn(mth, useInsn2, regionSubBlockNodes);
//							IContainer hashEqContainer= RegionUtils.getBlockContainer(hashSwitch2, hashEqBlock);
//							IContainer strEqContainer;
//							if (hashEqContainer instanceof IfRegion) {
//								IfRegion ir = (IfRegion) hashEqContainer;
//								strEqContainer = neg ? ir.getElseRegion() : ir.getThenRegion();
//							} else {
//								return false;
//							}
//
//							// TODO 多个 key 对应一个 container 是怎么处理的？还有 default
//							if (strEqContainer == null) {
//
//							}
//
//							// TODO 一个 int 的 case 里可能包含多个字符串比较（字符串的 hash 相同）
//							hashCases.add(new SwitchRegion.CaseInfo(List.of(key), strEqContainer));
//						}
//					}
//					// 找到判断条件里的两个 arg, 第一个应该是 RegisterArg, 其 SVar 赋值来自 str.hashCode()，第二个是 int 常量
//					// 第一个 arg 的 SVar.useList, 就是第一个 switch 的几个 case 的地方，再获取其 then/else region 创建 CaseInfo 就行了
//					IfCondition condition = Objects.requireNonNull(hashSwitch2.getCondition());
//					boolean neg = false;
//					if (condition.getMode() == IfCondition.Mode.NOT) {
//						condition = condition.getArgs().get(0);
//						neg = true;
//					}
//					if (condition.getMode() != IfCondition.Mode.COMPARE) {
//						return false;
//					}
//				}




//				{
//					IfRegion hashSwitch2 = (IfRegion) hashSwitch;
//					IfCondition condition = Objects.requireNonNull(hashSwitch2.getCondition());
//					boolean neg = false;
//					// 存储目标字符串 hashcode 的 arg
//					RegisterArg targetStrHashArg = null;
//
//					if (condition.getMode() == IfCondition.Mode.NOT) {
//						condition = condition.getArgs().get(0);
//						neg = true;
//					}
//
//					Compare compare = condition.getCompare();
//					if (compare == null) {
//						return false;
//					}
//					// TODO 给第一个 insn 也做通用处理
//					IfNode ifInsn = compare.getInsn();
//					if (ifInsn.getArgsCount() < 2) {
//						return false;
//					}
//
//					strArg = getStrHashCodeArg(ifInsn.getArg(0));
//					if (strArg == null) {
//						return false;
//					}
//					SSAVar strVar = strArg.getSVar();
//
//					// 1st arg is targetStr hashCode, 2nd arg is keyStr hashcode
//					RegisterArg currTargetStrHashArg = Utils.cast(ifInsn.getArg(0), RegisterArg.class);
//					LiteralArg currKeyStrHashArg = Utils.cast(ifInsn.getArg(1), LiteralArg.class);
//					if (currTargetStrHashArg == null || currKeyStrHashArg == null) {
//						return false;
//					}
//					if (targetStrHashArg == null) {
//						targetStrHashArg = currTargetStrHashArg;
//					} else if (targetStrHashArg != currTargetStrHashArg) {
//						return false;
//					}
//
//					int keyStrHash = (int) currKeyStrHashArg.getLiteral();
//					// get eqHashBranch to get some str.equals() if
//					// in this if's then block only 1 insn which is assign an index of 2nd switch
//					// the other branch is the next case
//					if (ifInsn.getOp() == IfOp.NE) {
//						neg = !neg;
//					}
//					IContainer eqHashBranch = neg ? hashSwitch2.getElseRegion() : hashSwitch2.getThenRegion();
//					IContainer neHashBranch = neg ? hashSwitch2.getThenRegion() : hashSwitch2.getElseRegion();
//
//					// 参考 processCase
//					// find str.equals() ifInsns
//					AtomicBoolean fail = new AtomicBoolean(false);
//					RegionUtils.visitBlockNodes(mth, eqHashBranch, blockNode -> {
//						if (fail.get()) {
//							return;
//						}
//						for (InsnNode insn : blockNode.getInstructions()) {
//							IfNode strEqualsIfInsn = Utils.cast(insn, IfNode.class);
//							// 获取字符串。参考 collectEqualsInsns
//							String keyStr = null;
//							if (strEqualsIfInsn != null) {
//								InsnWrapArg firstArg = Utils.cast(ifInsn.getArg(0), InsnWrapArg.class);
//								if (firstArg != null) {
//									// String.equals(), 1st arg is targetStr, 2nd arg is keyStr
//									InvokeNode strEqualsInvoke = Utils.cast(firstArg.getWrapInsn(), InvokeNode.class);
//									if (strEqualsInvoke != null && strEqualsInvoke.getCallMth().getRawFullId().equals("java.lang.String.equals(Ljava/lang/Object;)Z")) {
//										Object strValue = InsnUtils.getConstValueByArg(mth.root(), strEqualsInvoke.getArg(1));
//										if (strValue instanceof String) {
//											keyStr = (String) strValue;
//										}
//									}
//								}
//							}
//							if (keyStr == null) {
//								return;
//							}
//						}
//					});
//					if (fail.get()) {
//						return false;
//					}
//				}



				// 到 nextContainer 为 codeSwitch 为止

				// TODO


				SwitchStringAttr attr = codeSwitch.getHeader().get(AType.SWITCH_STRING);
				if (attr == null) {
					return false;
				}
				IfRegion hashSwitch2 = (IfRegion) hashSwitch;
				IfCondition condition = Objects.requireNonNull(hashSwitch2.getCondition());
				InsnNode ifInsn = Objects.requireNonNull(condition.getCompare()).getInsn();
				RegisterArg strHashArg = (RegisterArg) ifInsn.getArg(0);
				strArg = Objects.requireNonNull(getStrFromInsn(strHashArg.getAssignInsn()));
				SSAVar strVar = strArg.getSVar();
				Map<InsnNode, String> strEqInsns = collectEqualsInsns(mth, strVar);
				List<SwitchStringAttr.Case> attrCases = attr.getAllCases();

				switchData = new SwitchData(mth, hashSwitch);
				switchData.setNumArg((RegisterArg) codeSwInsn.getArg(0));
				switchData.setStrEqInsns(strEqInsns);
				switchData.setCases(new ArrayList<>(attrCases.size()));
				RegionUtils.visitBlockNodes(mth, hashSwitch2, block -> {
					switchData.getToRemove().addAll(block.getInstructions());
				});
				for (SwitchStringAttr.Case caseInfo : attrCases) {
					CaseData caseData = new CaseData();
					caseData.setCodeNum(caseInfo.getNumKeyIn2ndSwitch());
					caseData.getStrValues().addAll(caseInfo.getStrs());
					switchData.getCases().add(caseData);
				}
//				return false;

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
			codeSwInsn.replaceArg(codeSwInsn.getArg(0), strArg.duplicate());
			return true;
		} catch (StackOverflowError | Exception e) {
			mth.addWarnComment("Failed to restore switch over string. Please report as a decompilation issue", e);
			return false;
		}
	}

	// 如果 NOT 和 NE 共同出现的时候？
	private static void splitCondition(
			SplitConditions splitData,IfCondition condition) {
		if (condition == null) {
			return;
		}
		if (condition.getMode() == IfCondition.Mode.COMPARE) {
			if (condition.getCompare().getOp() == IfOp.NE) {
				splitData.addNE(condition);
			} else if (condition.getCompare().getOp() == IfOp.EQ) {
				splitData.addEQ(condition);
			} else {
				return;
			}
		} else if (condition.getMode() == IfCondition.Mode.NOT) {
			splitData.NOT();
			IfCondition innerCondition = condition.getArgs().get(0);
			splitCondition(splitData, innerCondition);
		} else {
			return;
		}
	}

	private static final class SplitConditions {
		List<IfCondition> list = new ArrayList<>();
		// IfCondition 如果是 not，后续添加的 condition 都要反过来。允许多次 not.
		boolean not = false;
		// 只能翻转一次。如果翻转过了还不满足条件就不行了
		boolean inverted = false;
		int eqCount = 0;
		int neCount = 0;
		// 如果已经添加了 ne,则返回 false
		public boolean addEQ(IfCondition c) {
			return not ? addNEInner(c) : addEQInner(c);
		}
		private boolean addEQInner(IfCondition c) {
			list.add(c);
			eqCount ++;
			return neCount == 0;
		}
		public boolean addNE(IfCondition c) {
			return not ? addEQInner(c) : addNEInner(c);

		}
		public boolean addNEInner(IfCondition c) {
			list.add(c);
			neCount ++;
			inverted = true;
			return eqCount == 0;
		}
		public void NOT() {
			not = !not;
		}
		// 确保拆分后的每个condition都是EQ或NE
		public boolean isValid() {
			return (eqCount != 0 && neCount == 0 && !inverted)
					|| (eqCount == 0 && neCount != 0 && inverted);
		}
		public IContainer getEQBranch(IfCondition condition) {
			Compare compare = condition.getCompare();
			if (!isValid() || !list.contains(condition) || compare == null)
				throw new JadxRuntimeException("Not valid");
			return inverted ? compare.getInsn().getElseBlock() : compare.getInsn().getThenBlock();
		}
		public void reset() {
			list.clear();
			inverted = false;
			eqCount = 0;
			neCount = 0;
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
			// keep second switch header, which used as replaced switchRegion header
			for (InsnNode secondHeader : switchData.getCodeSwitch().getHeader().getInstructions()) {
				secondHeader.remove(AFlag.REMOVE);
			}
			InsnRemover.removeAllMarked(mth);
		} catch (StackOverflowError | Exception e) {
			mth.addWarnComment("Failed to clean up code after switch over string restore", e);
		}
	}

	private boolean setCodeNum(SwitchData switchData) {
		RegisterArg numArg = switchData.getNumArg();
		List<CaseData> cases = switchData.getCases();
		// search index assign in cases code
		int extracted = 0;
		for (CaseData caseData : cases) {
			InsnNode numInsn = searchConstInsn(switchData, caseData, numArg);
			Integer num = extractConstNumber(switchData, numInsn, numArg);
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

	private @Nullable Integer extractConstNumber(SwitchData switchData, @Nullable InsnNode numInsn, RegisterArg numArg) {
		if (numInsn == null || numInsn.getArgsCount() != 1) {
			return null;
		}
		Object constVal = InsnUtils.getConstValueByArg(switchData.getMth().root(), numInsn.getArg(0));
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

	private boolean processCase(SwitchData switchData, SwitchRegion.CaseInfo caseInfo) {
		if (caseInfo.isDefaultCase()) {
			CaseData caseData = new CaseData();
			caseData.setCode(caseInfo.getContainer());
			return true;
		}
		AtomicBoolean fail = new AtomicBoolean(false);
		RegionUtils.visitRegions(switchData.getMth(), caseInfo.getContainer(), region -> {
			if (fail.get()) {
				return false;
			}
			if (region instanceof IfRegion) {
				CaseData caseData = fillCaseData((IfRegion) region, switchData);
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

	private @Nullable CaseData fillCaseData(IfRegion ifRegion, SwitchData switchData) {
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
		return caseData;
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

	public static @Nullable RegisterArg getStrFromInsn(@Nullable InsnNode insn) {
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
}
