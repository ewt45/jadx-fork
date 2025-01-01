package jadx.core.dex.visitors.regions.maker;

import java.util.ArrayList;
import java.util.List;
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
import jadx.core.dex.instructions.IfNode;
import jadx.core.dex.instructions.InsnType;
import jadx.core.dex.instructions.args.InsnArg;
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
import jadx.core.utils.BlockUtils;
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
		//为什么为null就一定要反转呢？？
		IfInfo mergedIf = mergeNestedIfNodes(currentIf);//为null了。确实也没有子if
		if (mergedIf != null) {
			currentIf = mergedIf;
		} else {
			// invert simple condition (compiler often do it)
			currentIf = IfInfo.invert(currentIf);
		} 
		// restructureIf里面badElse了导致置null被放到if外面
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
		//这一顿操作下来本来else的置null被放外面了。后面还能被放回来？还是压根不应该放外面

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

		//先设置一下
		info.setOutBlock(BlockUtils.getPathCross(mth, thenBlock, elseBlock));
		

		boolean badThen = isBadBranchBlock(info, thenBlock);//false
		//true elseBlock是viewFacade置null，其被调用处一个是这里的if的else，另一个是then里的catch块，不知为何then里没有trycatch块，导致catch块那个调用处被认为是if之外的地方了，因此这里为true
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
		} else {
			info.setOutBlock(BlockUtils.getPathCross(mth, thenBlock, elseBlock));
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
		//此函数之前设置好outBlock，这里直接比较分支是否是out。但是必须要out存在 比较结果才是正确的
		if (info.getOutBlock() != null) {
			return block == info.getOutBlock();
		}
		return !allPathsFromIf(block, info);
	}


	private static boolean allPathsFromIf(BlockNode block, IfInfo info) {

		// 作为out的else块。它应该是then的结尾的下一句。但是pathCross为null，因为
		// 从else和then的下一句的id（dominateFrontier)开始比较，而忽略了else本身。换句话说，如果else本身id作为
		// bitset，和then的下一句的bidset开始比较，而得出的block是else本身，那就说明else应该为out


		List<BlockNode> preds = block.getPredecessors();
		List<BlockNode> ifBlocks = info.getMergedBlocks();
		for (BlockNode pred : preds) {
			if (pred.contains(AFlag.LOOP_END)) {
				// ignore loop back edge
				continue;
			} 
			BlockNode top = BlockUtils.skipSyntheticPredecessor(pred);
			if (!ifBlocks.contains(top)) {
				return false;
			}

			

			// //如果不存在，需要判断是否一定从if开头能走到
			// for (BlockNode ifBlock : ifBlocks) {
			// 	if (ifBlock != top && top.isDominator(ifBlock)) {
			// 		return false;
			// 	}
			// }
			
			// //如果来自catch的那个，父块可能追溯到if吗？用父块比较？
			// boolean contained = false;
			// do {
			// 	if (ifBlocks.contains(top)) {
			// 		contained = true;
			// 		break;
			// 	} else if (top.getPredecessors().size() > 0) {
			// 		top = top.getPredecessors().get(0);
			// 	} else {
			// 		break;
			// 	}
			// } while (top.getPredecessors().size() > 0);
			// if (!contained) {
			// 	return false;
			// }
		}
		return true;
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
				return null;//then和else的getNextIf都是null，这里直接返回了。好像也没什么问题 if里也确实没有子if
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
		if (next.getPredecessors().size() != 1) {
			return null;
		}
		if (next.contains(AFlag.ADDED_TO_REGION)) {
			return null;
		}
		List<InsnNode> insns = block.getInstructions();
		boolean pass = true;
		List<InsnNode> forceInlineInsns = new ArrayList<>();
		if (!insns.isEmpty()) {
			// check that all instructions can be inlined
			for (InsnNode insn : insns) {
				RegisterArg res = insn.getResult();
				if (res == null) {
					pass = false;
					break;
				}
				List<RegisterArg> useList = res.getSVar().getUseList();
				int useCount = useList.size();
				if (useCount == 0) {
					// TODO?
					pass = false;
					break;
				}
				InsnArg arg = useList.get(0);
				InsnNode usePlace = arg.getParentInsn();
				if (!BlockUtils.blockContains(block, usePlace)
						&& !BlockUtils.blockContains(next, usePlace)) {
					pass = false;
					break;
				}
				if (useCount > 1) {
					forceInlineInsns.add(insn);
				} else {
					// allow only forced assign inline
					pass = false;
				}
			}
		}
		if (!pass) {
			return null;
		}
		IfInfo nextInfo = makeIfInfo(info.getMth(), next);
		if (nextInfo == null) {
			return getNextIfNodeInfo(info, next);
		}
		nextInfo.addInsnsForForcedInline(forceInlineInsns);
		return nextInfo;
	}
}
