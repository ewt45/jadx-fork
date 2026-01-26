package jadx.core.dex.visitors.regions.maker;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import jadx.core.Consts;
import jadx.core.dex.attributes.AFlag;
import jadx.core.dex.attributes.AType;
import jadx.core.dex.attributes.nodes.EdgeInsnAttr;
import jadx.core.dex.attributes.nodes.LoopInfo;
import jadx.core.dex.attributes.nodes.SwitchStringAttr;
import jadx.core.dex.instructions.IfNode;
import jadx.core.dex.instructions.IfOp;
import jadx.core.dex.instructions.InsnType;
import jadx.core.dex.instructions.InvokeNode;
import jadx.core.dex.instructions.SwitchInsn;
import jadx.core.dex.instructions.args.InsnArg;
import jadx.core.dex.instructions.args.InsnWrapArg;
import jadx.core.dex.instructions.args.LiteralArg;
import jadx.core.dex.instructions.args.RegisterArg;
import jadx.core.dex.nodes.BlockNode;
import jadx.core.dex.nodes.IRegion;
import jadx.core.dex.nodes.InsnNode;
import jadx.core.dex.nodes.MethodNode;
import jadx.core.dex.regions.Region;
import jadx.core.dex.regions.conditions.IfCondition;
import jadx.core.dex.regions.conditions.IfInfo;
import jadx.core.dex.regions.conditions.IfRegion;
import jadx.core.dex.regions.loops.LoopRegion;
import jadx.core.dex.trycatch.ExcHandlerAttr;
import jadx.core.dex.visitors.regions.SwitchOverStringVisitor;
import jadx.core.utils.BlockUtils;
import jadx.core.utils.InsnUtils;
import jadx.core.utils.Utils;
import jadx.core.utils.blocks.BlockSet;
import jadx.core.utils.exceptions.JadxRuntimeException;

import static jadx.core.utils.BlockUtils.isEqualPaths;
import static jadx.core.utils.BlockUtils.isEqualReturnBlocks;
import static jadx.core.utils.BlockUtils.isPathExists;

final class IfRegionMaker {
	private static final Logger LOG = LoggerFactory.getLogger(IfRegionMaker.class);
	private final MethodNode mth;
	private final RegionMaker regionMaker;

	IfRegionMaker(MethodNode mth, RegionMaker regionMaker) {
		this.mth = mth;
		this.regionMaker = regionMaker;
	}

	BlockNode process(IRegion currentRegion, BlockNode block, IfNode ifnode, RegionStack stack) {
		if (block.contains(AFlag.ADDED_TO_REGION)) {
			// block already included in other 'if' region
			return ifnode.getThenBlock();
		}

		IfInfo currentIf = makeIfInfo(mth, block);
		if (currentIf == null) {
			return null;
		}
		// 如果对比 hashcode, 可能是 switch over string, 在结构改变前先读取并保存数据
		if (currentIf.getMth().root().getArgs().isRestoreSwitchOverString()){
			preProcessSwitchStringFirstIf(currentIf);
		}
		IfInfo mergedIf = mergeNestedIfNodes(currentIf);
		if (mergedIf != null) {
			currentIf = mergedIf;
		} else {
			// invert simple condition (compiler often do it)
			currentIf = IfInfo.invert(currentIf);
		}
		IfInfo modifiedIf = restructureIf(mth, block, currentIf);
		if (modifiedIf != null) {
			currentIf = modifiedIf;
		} else {
			if (currentIf.getMergedBlocks().size() <= 1) {
				return null;
			}
			currentIf = makeIfInfo(mth, block);
			currentIf = restructureIf(mth, block, currentIf);
			if (currentIf == null) {
				// all attempts failed
				return null;
			}
		}
		confirmMerge(currentIf);

		IfRegion ifRegion = new IfRegion(currentRegion);
		ifRegion.updateCondition(currentIf);
		currentRegion.getSubBlocks().add(ifRegion);

		BlockNode outBlock = currentIf.getOutBlock();
		stack.push(ifRegion);
		stack.addExit(outBlock);

		BlockNode thenBlock = currentIf.getThenBlock();
		if (thenBlock == null) {
			// empty then block, not normal, but maybe correct
			ifRegion.setThenRegion(new Region(ifRegion));
		} else {
			ifRegion.setThenRegion(regionMaker.makeRegion(thenBlock));
		}
		BlockNode elseBlock = currentIf.getElseBlock();
		if (elseBlock == null || stack.containsExit(elseBlock)) {
			ifRegion.setElseRegion(null);
		} else {
			ifRegion.setElseRegion(regionMaker.makeRegion(elseBlock));
		}

		// insert edge insns in new 'else' branch
		// TODO: make more common algorithm
		if (ifRegion.getElseRegion() == null && outBlock != null) {
			List<EdgeInsnAttr> edgeInsnAttrs = outBlock.getAll(AType.EDGE_INSN);
			if (!edgeInsnAttrs.isEmpty()) {
				Region elseRegion = new Region(ifRegion);
				for (EdgeInsnAttr edgeInsnAttr : edgeInsnAttrs) {
					if (edgeInsnAttr.getEnd().equals(outBlock)) {
						addEdgeInsn(currentIf, elseRegion, edgeInsnAttr);
					}
				}
				ifRegion.setElseRegion(elseRegion);
			}
		}

		stack.pop();
		return outBlock;
	}

	@NotNull
	IfInfo buildIfInfo(LoopRegion loopRegion) {
		IfInfo condInfo = makeIfInfo(mth, loopRegion.getHeader());
		condInfo = searchNestedIf(condInfo);
		confirmMerge(condInfo);
		return condInfo;
	}

	private void addEdgeInsn(IfInfo ifInfo, Region region, EdgeInsnAttr edgeInsnAttr) {
		BlockNode start = edgeInsnAttr.getStart();
		boolean fromThisIf = false;
		for (BlockNode ifBlock : ifInfo.getMergedBlocks()) {
			if (ifBlock.getSuccessors().contains(start)) {
				fromThisIf = true;
				break;
			}
		}
		if (!fromThisIf) {
			return;
		}
		region.add(start);
	}

	@Nullable
	static IfInfo makeIfInfo(MethodNode mth, BlockNode ifBlock) {
		InsnNode lastInsn = BlockUtils.getLastInsn(ifBlock);
		if (lastInsn == null || lastInsn.getType() != InsnType.IF) {
			return null;
		}
		IfNode ifNode = (IfNode) lastInsn;
		IfCondition condition = IfCondition.fromIfNode(ifNode);
		IfInfo info = new IfInfo(mth, condition, ifNode.getThenBlock(), ifNode.getElseBlock());
		info.getMergedBlocks().add(ifBlock);
		return info;
	}

	static IfInfo searchNestedIf(IfInfo info) {
		IfInfo next = mergeNestedIfNodes(info);
		if (next != null) {
			return next;
		}
		return info;
	}

	static IfInfo restructureIf(MethodNode mth, BlockNode block, IfInfo info) {
		BlockNode thenBlock = info.getThenBlock();
		BlockNode elseBlock = info.getElseBlock();

		if (Objects.equals(thenBlock, elseBlock)) {
			IfInfo ifInfo = new IfInfo(info, null, null);
			ifInfo.setOutBlock(thenBlock);
			return ifInfo;
		}

		// select 'then', 'else' and 'exit' blocks
		if (thenBlock.contains(AFlag.RETURN) && elseBlock.contains(AFlag.RETURN)) {
			info.setOutBlock(null);
			return info;
		}
		// init outblock, which will be used in isBadBranchBlock to compare with branch block
		info.setOutBlock(BlockUtils.getPathCross(mth, thenBlock, elseBlock));
		boolean badThen = isBadBranchBlock(info, thenBlock);
		boolean badElse = isBadBranchBlock(info, elseBlock);
		if (badThen && badElse) {
			if (Consts.DEBUG_RESTRUCTURE) {
				LOG.debug("Stop processing blocks after 'if': {}, method: {}", info.getMergedBlocks(), mth);
			}
			return null;
		}
		if (badElse) {
			info = new IfInfo(info, thenBlock, null);
			info.setOutBlock(elseBlock);
		} else if (badThen) {
			info = IfInfo.invert(info);
			info = new IfInfo(info, elseBlock, null);
			info.setOutBlock(thenBlock);
		}

		// getPathCross may not find outBlock (e.g. one branch has return, outBlock definitely is
		// null), so should check further
		if (info.getOutBlock() == null) {
			BlockNode scopeOutBlockThen = findScopeOutBlock(mth, info.getThenBlock());
			BlockNode scopeOutBlockElse = findScopeOutBlock(mth, info.getElseBlock());
			if (scopeOutBlockThen == null && scopeOutBlockElse != null) {
				info.setOutBlock(scopeOutBlockElse);
			} else if (scopeOutBlockThen != null && scopeOutBlockElse == null) {
				info.setOutBlock(scopeOutBlockThen);
			} else if (scopeOutBlockThen != null && scopeOutBlockThen == scopeOutBlockElse) {
				info.setOutBlock(scopeOutBlockThen);
			}
		}

		if (BlockUtils.isBackEdge(block, info.getOutBlock())) {
			info.setOutBlock(null);
		}
		return info;
	}

	private static boolean isBadBranchBlock(IfInfo info, BlockNode block) {
		// check if block at end of loop edge
		if (block.contains(AFlag.LOOP_START) && block.getPredecessors().size() == 1) {
			BlockNode pred = block.getPredecessors().get(0);
			if (pred.contains(AFlag.LOOP_END)) {
				List<LoopInfo> startLoops = block.getAll(AType.LOOP);
				List<LoopInfo> endLoops = pred.getAll(AType.LOOP);
				// search for same loop
				for (LoopInfo startLoop : startLoops) {
					for (LoopInfo endLoop : endLoops) {
						if (startLoop == endLoop) {
							return true;
						}
					}
				}
			}
		}
		// if branch block itself is outblock
		if (info.getOutBlock() != null) {
			return block == info.getOutBlock();
		}
		return !allPathsFromIf(block, info);
	}

	private static boolean allPathsFromIf(BlockNode block, IfInfo info) {
		List<BlockNode> preds = block.getPredecessors();
		BlockSet ifBlocks = info.getMergedBlocks();
		for (BlockNode pred : preds) {
			if (pred.contains(AFlag.LOOP_END)) {
				// ignore loop back edge
				continue;
			}
			BlockNode top = BlockUtils.skipSyntheticPredecessor(pred);
			if (!ifBlocks.contains(top)) {
				return false;
			}
		}
		return true;
	}

	/**
	 * if startBlock is in a (try) scope, find the scope end as outBlock
	 */
	private @Nullable static BlockNode findScopeOutBlock(MethodNode mth, BlockNode startBlock) {
		if (startBlock == null) {
			return null;
		}
		List<BlockNode> domFrontiers = BlockUtils.bitSetToBlocks(mth, startBlock.getDomFrontier());
		BlockNode scopeOutBlock = null;

		// find handler from domFrontier(could be scope end), if domFrontier is handler
		// and its topSplitter dominates branch block, then branch should end
		for (BlockNode domFrontier : domFrontiers) {
			ExcHandlerAttr handler = domFrontier.get(AType.EXC_HANDLER);
			if (handler == null) {
				continue;
			}
			BlockNode topSplitter = handler.getTryBlock().getTopSplitter();
			if (startBlock.isDominator(topSplitter)) {
				scopeOutBlock = BlockUtils.getTryAndHandlerCrossBlock(mth, handler.getHandler());
				break;
			}
		}

		return scopeOutBlock;
	}

	static IfInfo mergeNestedIfNodes(IfInfo currentIf) {
		BlockNode curThen = currentIf.getThenBlock();
		BlockNode curElse = currentIf.getElseBlock();
		if (curThen == curElse) {
			return null;
		}
		if (BlockUtils.isFollowBackEdge(curThen)
				|| BlockUtils.isFollowBackEdge(curElse)) {
			return null;
		}
		boolean followThenBranch;
		IfInfo nextIf = getNextIf(currentIf, curThen);
		if (nextIf != null) {
			followThenBranch = true;
		} else {
			nextIf = getNextIf(currentIf, curElse);
			if (nextIf != null) {
				followThenBranch = false;
			} else {
				return null;
			}
		}

		boolean assignInlineNeeded = !nextIf.getForceInlineInsns().isEmpty();
		if (assignInlineNeeded) {
			for (BlockNode mergedBlock : currentIf.getMergedBlocks()) {
				if (mergedBlock.contains(AFlag.LOOP_START)) {
					// don't inline assigns into loop condition
					return currentIf;
				}
			}
		}

		if (isInversionNeeded(currentIf, nextIf)) {
			// invert current node for match pattern
			nextIf = IfInfo.invert(nextIf);
		}
		boolean thenPathSame = isEqualPaths(curThen, nextIf.getThenBlock());
		boolean elsePathSame = isEqualPaths(curElse, nextIf.getElseBlock());
		if (!thenPathSame && !elsePathSame) {
			// complex condition, run additional checks
			if (checkConditionBranches(curThen, curElse)
					|| checkConditionBranches(curElse, curThen)) {
				return null;
			}
			BlockNode otherBranchBlock = followThenBranch ? curElse : curThen;
			otherBranchBlock = BlockUtils.followEmptyPath(otherBranchBlock);
			if (!isPathExists(nextIf.getFirstIfBlock(), otherBranchBlock)) {
				return checkForTernaryInCondition(currentIf);
			}

			// this is nested conditions with different mode (i.e (a && b) || c),
			// search next condition for merge, get null if failed
			IfInfo tmpIf = mergeNestedIfNodes(nextIf);
			if (tmpIf != null) {
				nextIf = tmpIf;
				if (isInversionNeeded(currentIf, nextIf)) {
					nextIf = IfInfo.invert(nextIf);
				}
				if (!canMerge(currentIf, nextIf, followThenBranch)) {
					return currentIf;
				}
			} else {
				return currentIf;
			}
		} else {
			if (assignInlineNeeded) {
				boolean sameOuts = (thenPathSame && !followThenBranch) || (elsePathSame && followThenBranch);
				if (!sameOuts) {
					// don't inline assigns inside simple condition
					currentIf.resetForceInlineInsns();
					return currentIf;
				}
			}
		}

		IfInfo result = mergeIfInfo(currentIf, nextIf, followThenBranch);
		// search next nested if block
		return searchNestedIf(result);
	}

	private static IfCondition unwrapNOT2Compare(IfCondition c) {
		if (c.getMode() == IfCondition.Mode.COMPARE) {
			return c;
		} else if (c.getMode() == IfCondition.Mode.NOT) {
			c = c.getArgs().get(0);
			return unwrapNOT2Compare(c);
		} else {
			return null;
		}
	}

	private static @Nullable BlockNode getBranchBlockSkipEmpty(IfNode ifInsn, boolean then) {
		BlockNode b = then ? ifInsn.getThenBlock() : ifInsn.getElseBlock();
		while (b != null && b.getInstructions().isEmpty()) {
			if (b.isMthExitBlock()) {
				b = null;
				break;
			}
			b = BlockUtils.getNextBlock(b);
		}
		return b;
	}
	private static @Nullable BlockNode getNextBlockSkipEmpty(BlockNode b) {
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
	// 参考 SwitchOverStringVisitor
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

	// e.g. 'if (str.equals("aa") == true)'. return insn of 'str.equals("aa")'
	private static @Nullable InvokeNode getStrEqInvokeFromIfInsn(IfNode strIfInsn) {
		if (strIfInsn.getOp() != IfOp.EQ && strIfInsn.getOp() != IfOp.NE) {
			return null;
		}
		boolean neg;
		if (strIfInsn.getOp() == IfOp.EQ) {
			neg = false;
		} else if (strIfInsn.getOp() == IfOp.NE) {
			neg = true;
		} else {
			return null;
		}
		if (strIfInsn.getArg(1).isFalse()) {
			neg = !neg;
		}

		InsnWrapArg strCmpArg = Utils.cast(strIfInsn.getArg(0), InsnWrapArg.class);
		InvokeNode eqIvkInsn = strCmpArg == null ? null : Utils.cast(strCmpArg.getWrapInsn(), InvokeNode.class);
		if (eqIvkInsn == null || eqIvkInsn.getType() != InsnType.INVOKE
				|| !eqIvkInsn.getCallMth().getRawFullId().equals("java.lang.String.equals(Ljava/lang/Object;)Z")) {
			eqIvkInsn =  null;
		}
		return eqIvkInsn;
	}
	private static @Nullable RegisterArg getNumArgIn2ndSwitch(BlockNode switchBlock) {
		SwitchInsn insn = (SwitchInsn) BlockUtils.getLastInsnWithType(switchBlock, InsnType.SWITCH);
		if (insn != null) {
			return Utils.cast(insn.getArg(0), RegisterArg.class);
		} else {
			return null;
		}
	}
	// TODO 确保此函数中的 while 不会死循环？
	private static void preProcessSwitchStringFirstIf(IfInfo currentIf) {
		IfCondition condition = unwrapNOT2Compare(currentIf.getCondition());
		if (condition == null) {
			return;
		}
		IfNode hashIfInsn = condition.getCompare().getInsn();
		if (hashIfInsn.getArgsCount() < 2) {
			return;
		}

		MethodNode mth = currentIf.getMth();
		// if 后应该是 switch
		BlockNode secondSwitchBlock = BlockUtils.getPathCross(mth, currentIf.getThenBlock(), currentIf.getElseBlock());
		// 存储第二个 switch 的判断的 arg
		RegisterArg numArg = getNumArgIn2ndSwitch(secondSwitchBlock);
		if (secondSwitchBlock == null || numArg == null
				|| secondSwitchBlock.get(AType.SWITCH_STRING) != null) {
			return;
		}

		// 存储目标字符串 hashcode 的 arg
		RegisterArg targetStrHashArg = null;
		// 存储目标字符串对象的 arg
		RegisterArg targetStrArg = null;

		// 存储每个 hash 比较成功后进入的分支。里面应该有字符串比较和第二个 switch 的 index 赋值
		// key 正常为 Integer, 如果是 default 分支则为 Object
		Map<Object, BlockNode> strCompareMap = new HashMap<>();
		Object defaultKeyIn1stStage = new Object();

		boolean neg = condition != currentIf.getCondition();

		// 遍历 外层 if （比较 hashcode），记录内层 if（比较字符串）和第二个 switch
		while (true) {
			// 1st arg is targetStr hashCode, 2nd arg is keyStr hashcode
			RegisterArg currTargetStrHashArg = Utils.cast(hashIfInsn.getArg(0), RegisterArg.class);
			LiteralArg currKeyStrHashArg = Utils.cast(hashIfInsn.getArg(1), LiteralArg.class);
			if (currTargetStrHashArg == null || currKeyStrHashArg == null) {
				return;
			}
			if (targetStrHashArg == null) {
				targetStrHashArg = currTargetStrHashArg;
				targetStrArg = SwitchOverStringVisitor.getStrFromInsn(targetStrHashArg.getAssignInsn());
				if (targetStrArg == null) {
					return;
				}
			} else if (!targetStrHashArg.equals(currTargetStrHashArg)) {
				return;
			}

			// get eqHashBranch to get some str.equals() if
			// in this if's then block only 1 insn which is assign an index of 2nd switch
			// the other branch is the next case
			if (hashIfInsn.getOp() == IfOp.NE) {
				neg = !neg;
			}

			// String.equals() 的 if
			BlockNode eqHashBranch = getBranchBlockSkipEmpty(hashIfInsn, !neg);
			// 下一个 hashcode 比较
			BlockNode neHashBranch = getBranchBlockSkipEmpty(hashIfInsn, neg);
			if (eqHashBranch == null || neHashBranch == null) {
				return;
			}

			// 先把内层 if 存起来，找到所有 hashcode 对比的分支以及第二个 switch 后再进一步处理
			int keyStrHash = (int) currKeyStrHashArg.getLiteral();
			strCompareMap.put(keyStrHash, eqHashBranch);

			InsnNode afterHashInsn = neHashBranch.getInstructions().get(0);
			// 下一个外层 if
			if (afterHashInsn instanceof IfNode) {
				hashIfInsn = (IfNode) afterHashInsn;
				neg = false;
				continue;
			}
			// 第一阶段的 default
			if (afterHashInsn.getType() == InsnType.CONST) {
				strCompareMap.put(defaultKeyIn1stStage, neHashBranch);
				neHashBranch = getNextBlockSkipEmpty(neHashBranch);
				if (neHashBranch == null) {
					return;
				}
				afterHashInsn = neHashBranch.getInstructions().get(0);
			}
			// 第一阶段结束，第二阶段的 switch
			if (afterHashInsn instanceof SwitchInsn) {
				// 第一阶段结束，第二阶段的 switch
				secondSwitchBlock = neHashBranch;
				numArg = Utils.cast(afterHashInsn.getArg(0), RegisterArg.class);
				if (numArg == null) {
					return;
				}
				break;
			} else {
				return;
			}
		}

		SwitchStringAttr attr = new SwitchStringAttr(secondSwitchBlock);

		// 遍历内层 if, 找到所有字符串对应第二个 switch 的 index, 并且确保内层 if结束的下一行是 switch
		// 确保外层 hashcode 确实是字符串的 hashcode
		for (Map.Entry<Object, BlockNode> entry : strCompareMap.entrySet()) {
			// default 分支
			if (entry.getKey() == defaultKeyIn1stStage) {
				BlockNode defaultBranch = entry.getValue();
				InsnNode assignIndexInsn = defaultBranch.getInstructions().get(0);
				if (assignIndexInsn.getType() != InsnType.CONST) {
					return;
				}

				// 确保下一行是第二个 switch
				if (getNextBlockSkipEmpty(defaultBranch) != secondSwitchBlock) {
					return;
				}

				// 记录 num 和对应的字符串。确认赋值的 arg 是同一个 numArg
				Integer num = extractConstNumber(mth, assignIndexInsn, numArg);
				if (num == null) {
					return;
				}
				attr.getCaseByNum(num).addStr(null);
				continue;
			}

			int strHash = (Integer) entry.getKey();
			BlockNode strCompareBlock = entry.getValue();
			IfNode strIfInsn = Utils.cast(strCompareBlock.getInstructions().get(0), IfNode.class);
			if (strIfInsn == null) {
				return;
			}

			if (strIfInsn.getOp() == IfOp.EQ) {
				neg = false;
			} else if (strIfInsn.getOp() == IfOp.NE) {
				neg = true;
			} else {
				return;
			}
			if (strIfInsn.getArg(1).isFalse()) {
				neg = !neg;
			}

			BlockNode eqStrBranch = getBranchBlockSkipEmpty(strIfInsn, !neg);
			BlockNode neStrBranch = getBranchBlockSkipEmpty(strIfInsn, neg);
			if (eqStrBranch == null || neStrBranch == null) {
				return;
			}
			// 确保进入 eqStr 后赋值完下一行是第二个 switch
			if (getNextBlockSkipEmpty(eqStrBranch) != secondSwitchBlock) {
				return;
			}

			// 获取字符串
			InvokeNode eqIvkInsn = getStrEqInvokeFromIfInsn(strIfInsn);
			if (eqIvkInsn == null) {
				return;
			}

			while (true) {
				// TODO 确认字符串寄存器是同一个
				// 第一个 arg 是目标字符串，第二个 arg 是常量字符串
				RegisterArg currStrArg = Utils.cast(eqIvkInsn.getInstanceArg(), RegisterArg.class);
				InsnArg secondArg = eqIvkInsn.getArg(1);
				String strValue = Utils.cast(InsnUtils.getConstValueByArg(mth.root(), secondArg), String.class);
				if (!targetStrArg.equals(currStrArg) || strValue == null || strValue.hashCode() != strHash) {
					return;
				}

				// 赋值第二个 switch 的 num
				InsnNode assignIndexInsn = eqStrBranch.getInstructions().get(0);
				if (assignIndexInsn.getType() != InsnType.CONST) {
					return;
				}

				// 记录 num 和对应的字符串。确认赋值的 arg 是同一个 numArg
				Integer num = extractConstNumber(mth, assignIndexInsn, numArg);
				if (num == null) {
					return;
				}
				attr.getCaseByNum(num).addStr(strValue);

				InsnNode neStrBranchInsn = neStrBranch.getInstructions().get(0);
				if (neStrBranchInsn instanceof IfNode) {
					// 相同 hashcode 的下一个字符串.equals() 判断
					eqIvkInsn = getStrEqInvokeFromIfInsn((IfNode) neStrBranchInsn);
					if (eqIvkInsn == null) {
						return;
					}
				} else if (neStrBranchInsn.getType() == InsnType.CONST) {
					// default 赋值，确保下一行是第二个 switch
					if (getNextBlockSkipEmpty(neStrBranch) != secondSwitchBlock) {
						return;
					}
					break;
				} else {
					return;
				}
			}
		}

		secondSwitchBlock.addAttr(attr);
	}

	private static IfInfo checkForTernaryInCondition(IfInfo currentIf) {
		IfInfo nextThen = getNextIf(currentIf, currentIf.getThenBlock());
		IfInfo nextElse = getNextIf(currentIf, currentIf.getElseBlock());
		if (nextThen == null || nextElse == null) {
			return null;
		}
		if (!nextThen.getFirstIfBlock().getDomFrontier().equals(nextElse.getFirstIfBlock().getDomFrontier())) {
			return null;
		}
		nextThen = searchNestedIf(nextThen);
		nextElse = searchNestedIf(nextElse);
		if (nextThen.getThenBlock() == nextElse.getThenBlock()
				&& nextThen.getElseBlock() == nextElse.getElseBlock()) {
			return mergeTernaryConditions(currentIf, nextThen, nextElse);
		}
		if (nextThen.getThenBlock() == nextElse.getElseBlock()
				&& nextThen.getElseBlock() == nextElse.getThenBlock()) {
			nextElse = IfInfo.invert(nextElse);
			return mergeTernaryConditions(currentIf, nextThen, nextElse);
		}
		return null;
	}

	private static IfInfo mergeTernaryConditions(IfInfo currentIf, IfInfo nextThen, IfInfo nextElse) {
		IfCondition newCondition = IfCondition.ternary(currentIf.getCondition(),
				nextThen.getCondition(), nextElse.getCondition());
		IfInfo result = new IfInfo(currentIf.getMth(), newCondition, nextThen.getThenBlock(), nextThen.getElseBlock());
		result.merge(currentIf, nextThen, nextElse);
		confirmMerge(result);
		return result;
	}

	private static boolean isInversionNeeded(IfInfo currentIf, IfInfo nextIf) {
		return isEqualPaths(currentIf.getElseBlock(), nextIf.getThenBlock())
				|| isEqualPaths(currentIf.getThenBlock(), nextIf.getElseBlock());
	}

	private static boolean canMerge(IfInfo a, IfInfo b, boolean followThenBranch) {
		if (followThenBranch) {
			return isEqualPaths(a.getElseBlock(), b.getElseBlock());
		} else {
			return isEqualPaths(a.getThenBlock(), b.getThenBlock());
		}
	}

	private static boolean checkConditionBranches(BlockNode from, BlockNode to) {
		return from.getCleanSuccessors().size() == 1 && from.getCleanSuccessors().contains(to);
	}

	static IfInfo mergeIfInfo(IfInfo first, IfInfo second, boolean followThenBranch) {
		MethodNode mth = first.getMth();
		Set<BlockNode> skipBlocks = first.getSkipBlocks();
		BlockNode thenBlock;
		BlockNode elseBlock;
		if (followThenBranch) {
			thenBlock = second.getThenBlock();
			elseBlock = getBranchBlock(first.getElseBlock(), second.getElseBlock(), skipBlocks, mth);
		} else {
			thenBlock = getBranchBlock(first.getThenBlock(), second.getThenBlock(), skipBlocks, mth);
			elseBlock = second.getElseBlock();
		}
		IfCondition.Mode mergeOperation = followThenBranch ? IfCondition.Mode.AND : IfCondition.Mode.OR;
		IfCondition condition = IfCondition.merge(mergeOperation, first.getCondition(), second.getCondition());
		IfInfo result = new IfInfo(mth, condition, thenBlock, elseBlock);
		result.merge(first, second);
		return result;
	}

	private static BlockNode getBranchBlock(BlockNode first, BlockNode second, Set<BlockNode> skipBlocks, MethodNode mth) {
		if (first == second) {
			return second;
		}
		if (isEqualReturnBlocks(first, second)) {
			skipBlocks.add(first);
			return second;
		}
		if (BlockUtils.isDuplicateBlockPath(first, second)) {
			first.add(AFlag.REMOVE);
			skipBlocks.add(first);
			return second;
		}
		BlockNode cross = BlockUtils.getPathCross(mth, first, second);
		if (cross != null) {
			BlockUtils.visitBlocksOnPath(mth, first, cross, skipBlocks::add);
			BlockUtils.visitBlocksOnPath(mth, second, cross, skipBlocks::add);
			skipBlocks.remove(cross);
			return cross;
		}
		BlockNode firstSkip = BlockUtils.followEmptyPath(first);
		BlockNode secondSkip = BlockUtils.followEmptyPath(second);
		if (firstSkip.equals(secondSkip) || isEqualReturnBlocks(firstSkip, secondSkip)) {
			skipBlocks.add(first);
			skipBlocks.add(second);
			BlockUtils.visitBlocksOnEmptyPath(first, skipBlocks::add);
			BlockUtils.visitBlocksOnEmptyPath(second, skipBlocks::add);
			return secondSkip;
		}
		throw new JadxRuntimeException("Unexpected merge pattern");
	}

	static void confirmMerge(IfInfo info) {
		if (info.getMergedBlocks().size() > 1) {
			for (BlockNode block : info.getMergedBlocks()) {
				if (block != info.getFirstIfBlock()) {
					block.add(AFlag.ADDED_TO_REGION);
				}
			}
		}
		if (!info.getSkipBlocks().isEmpty()) {
			for (BlockNode block : info.getSkipBlocks()) {
				block.add(AFlag.ADDED_TO_REGION);
			}
			info.getSkipBlocks().clear();
		}
		for (InsnNode forceInlineInsn : info.getForceInlineInsns()) {
			forceInlineInsn.add(AFlag.FORCE_ASSIGN_INLINE);
		}
	}

	private static IfInfo getNextIf(IfInfo info, BlockNode block) {
		if (!canSelectNext(info, block)) {
			return null;
		}
		return getNextIfNodeInfo(info, block);
	}

	private static boolean canSelectNext(IfInfo info, BlockNode block) {
		if (block.getPredecessors().size() == 1) {
			return true;
		}
		return info.getMergedBlocks().containsAll(block.getPredecessors());
	}

	private static IfInfo getNextIfNodeInfo(IfInfo info, BlockNode block) {
		if (block == null || block.contains(AType.LOOP) || block.contains(AFlag.ADDED_TO_REGION)) {
			return null;
		}
		InsnNode lastInsn = BlockUtils.getLastInsn(block);
		if (lastInsn != null && lastInsn.getType() == InsnType.IF) {
			return makeIfInfo(info.getMth(), block);
		}
		// skip this block and search in successors chain
		List<BlockNode> successors = block.getSuccessors();
		if (successors.size() != 1) {
			return null;
		}
		BlockNode next = successors.get(0);
		if (next.getPredecessors().size() != 1 || next.contains(AFlag.ADDED_TO_REGION)) {
			return null;
		}
		List<InsnNode> forceInlineInsns = new ArrayList<>();
		if (!checkInsnsInline(block, next, forceInlineInsns)) {
			return null;
		}
		IfInfo nextInfo = makeIfInfo(info.getMth(), next);
		if (nextInfo == null) {
			return getNextIfNodeInfo(info, next);
		}
		nextInfo.addInsnsForForcedInline(forceInlineInsns);
		return nextInfo;
	}

	/**
	 * Check that all instructions can be inlined
	 */
	private static boolean checkInsnsInline(BlockNode block, BlockNode next, List<InsnNode> forceInlineInsns) {
		List<InsnNode> insns = block.getInstructions();
		if (insns.isEmpty()) {
			return true;
		}
		boolean pass = true;
		for (InsnNode insn : insns) {
			RegisterArg res = insn.getResult();
			if (res == null) {
				return false;
			}
			List<RegisterArg> useList = res.getSVar().getUseList();
			int useCount = useList.size();
			if (useCount == 0) {
				// TODO?
				return false;
			}
			InsnArg arg = useList.get(0);
			InsnNode usePlace = arg.getParentInsn();
			if (!BlockUtils.blockContains(block, usePlace)
					&& !BlockUtils.blockContains(next, usePlace)) {
				return false;
			}
			if (useCount > 1) {
				forceInlineInsns.add(insn);
			} else {
				// allow only forced assign inline
				pass = false;
			}
		}
		return pass;
	}
}
