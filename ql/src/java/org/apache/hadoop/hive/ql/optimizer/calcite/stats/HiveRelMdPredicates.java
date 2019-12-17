/**
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.hadoop.hive.ql.optimizer.calcite.stats;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedMap;

import org.apache.calcite.linq4j.Linq4j;
import org.apache.calcite.linq4j.Ord;
import org.apache.calcite.linq4j.function.Predicate1;
import org.apache.calcite.plan.RelOptPredicateList;
import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.plan.hep.HepRelVertex;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.Aggregate;
import org.apache.calcite.rel.core.Join;
import org.apache.calcite.rel.core.JoinRelType;
import org.apache.calcite.rel.core.Project;
import org.apache.calcite.rel.core.SemiJoin;
import org.apache.calcite.rel.core.Union;
import org.apache.calcite.rel.metadata.BuiltInMetadata;
import org.apache.calcite.rel.metadata.ChainedRelMetadataProvider;
import org.apache.calcite.rel.metadata.MetadataDef;
import org.apache.calcite.rel.metadata.MetadataHandler;
import org.apache.calcite.rel.metadata.ReflectiveRelMetadataProvider;
import org.apache.calcite.rel.metadata.RelMdPredicates;
import org.apache.calcite.rel.metadata.RelMetadataProvider;
import org.apache.calcite.rel.metadata.RelMetadataQuery;
import org.apache.calcite.rex.RexBuilder;
import org.apache.calcite.rex.RexCall;
import org.apache.calcite.rex.RexInputRef;
import org.apache.calcite.rex.RexLiteral;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.rex.RexPermuteInputsShuttle;
import org.apache.calcite.rex.RexUtil;
import org.apache.calcite.rex.RexVisitorImpl;
import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.util.BitSets;
import org.apache.calcite.util.BuiltInMethod;
import org.apache.calcite.util.ImmutableBitSet;
import org.apache.calcite.util.mapping.Mapping;
import org.apache.calcite.util.mapping.MappingType;
import org.apache.calcite.util.mapping.Mappings;
import org.apache.hadoop.hive.ql.optimizer.calcite.HiveCalciteUtil;

import com.google.common.base.Function;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Iterators;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;


//TODO: Move this to calcite
public class HiveRelMdPredicates implements MetadataHandler<BuiltInMetadata.Predicates> {

  public static final RelMetadataProvider SOURCE =
          ChainedRelMetadataProvider.of(
                  ImmutableList.of(
                          ReflectiveRelMetadataProvider.reflectiveSource(
                                  BuiltInMethod.PREDICATES.method, new HiveRelMdPredicates()),
                          RelMdPredicates.SOURCE));

  private static final List<RexNode> EMPTY_LIST = ImmutableList.of();

  //~ Constructors -----------------------------------------------------------

  private HiveRelMdPredicates() {}

  //~ Methods ----------------------------------------------------------------

  @Override
  public MetadataDef<BuiltInMetadata.Predicates> getDef() {
    return BuiltInMetadata.Predicates.DEF;
  }

  /**
   * Infers predicates for a project.
   *
   * <ol>
   * <li>create a mapping from input to projection. Map only positions that
   * directly reference an input column.
   * <li>Expressions that only contain above columns are retained in the
   * Project's pullExpressions list.
   * <li>For e.g. expression 'a + e = 9' below will not be pulled up because 'e'
   * is not in the projection list.
   *
   * <pre>
   * childPullUpExprs:      {a &gt; 7, b + c &lt; 10, a + e = 9}
   * projectionExprs:       {a, b, c, e / 2}
   * projectionPullupExprs: {a &gt; 7, b + c &lt; 10}
   * </pre>
   *
   * </ol>
   */
  //Project是把所把调用链上所有的 常量搜齐
  public RelOptPredicateList getPredicates(Project project, RelMetadataQuery mq) {

    RelNode child = project.getInput();
    final RexBuilder rexBuilder = project.getCluster().getRexBuilder();
    RelOptPredicateList childInfo = mq.getPulledUpPredicates(child);


    List<RexNode> projectPullUpPredicates = new ArrayList<RexNode>();
    //源表的字段位置-输出（project）的位置
    HashMultimap<Integer, Integer> inpIndxToOutIndxMap = HashMultimap.create();
    ImmutableBitSet.Builder columnsMappedBuilder = ImmutableBitSet.builder();
    Mapping m = Mappings.create(MappingType.PARTIAL_FUNCTION, child.getRowType().getFieldCount(),
        project.getRowType().getFieldCount());
    System.out.printf("edwin getPredicates Project child is %s, class is %s \n",
            (child instanceof HepRelVertex)?((HepRelVertex) child).getCurrentRel().toString():child.toString(),
            (child instanceof HepRelVertex)?((HepRelVertex) child).getCurrentRel().getClass():child.getClass());
    System.out.printf("edwin getPredicates Project m.soucre is %d, target is %d \n",
            m.getSourceCount(), m.getTargetCount());

    //source:就是源表，比如源表有23字段
    //target是要映射的字段 比如映射3个
    for (Ord<RexNode> o : Ord.zip(project.getProjects())) {
      if (o.e instanceof RexInputRef) {
        //此处是把filter中条件的 引用位置记录次来，引用位置就是表中每个字段的位置
        //重点：引用类型就是把 当前关系中的字段位置记录起来
        int sIdx = ((RexInputRef) o.e).getIndex();
        m.set(sIdx, o.i);
        inpIndxToOutIndxMap.put(sIdx, o.i);
        columnsMappedBuilder.set(sIdx);
      }
    }

    // Go over childPullUpPredicates. If a predicate only contains columns in
    // 'columnsMapped' construct a new predicate based on mapping.
    final ImmutableBitSet columnsMapped = columnsMappedBuilder.build();
    for (RexNode r : childInfo.pulledUpPredicates) {
      //常量就没有占位
      //把引用位置记录起来，对比和上面记录的是否一致
      ImmutableBitSet rCols = RelOptUtil.InputFinder.bits(r);
      if (columnsMapped.contains(rCols)) {
        r = r.accept(new RexPermuteInputsShuttle(m, child));
        projectPullUpPredicates.add(r);
      }
    }

    System.out.printf("edwin before getPredicates Project  projectPullUpPredicates is %s\n",
            projectPullUpPredicates.toString());

    // Project can also generate constants. We need to include them.
    //把project中的常量搜集
    for (Ord<RexNode> expr : Ord.zip(project.getProjects())) {
      if (RexLiteral.isNullLiteral(expr.e)) {
        projectPullUpPredicates.add(rexBuilder.makeCall(SqlStdOperatorTable.IS_NULL,
            rexBuilder.makeInputRef(project, expr.i)));
      } else if (expr.e instanceof RexLiteral) {
        final RexLiteral literal = (RexLiteral) expr.e;
        projectPullUpPredicates.add(rexBuilder.makeCall(SqlStdOperatorTable.EQUALS,
            rexBuilder.makeInputRef(project, expr.i), literal));
      } else if (expr.e instanceof RexCall && HiveCalciteUtil.isDeterministicFuncOnLiterals(expr.e)) {
      //TODO: Move this to calcite
        projectPullUpPredicates.add(rexBuilder.makeCall(SqlStdOperatorTable.EQUALS,
            rexBuilder.makeInputRef(project, expr.i), expr.e));
      }
    }
    System.out.printf("edwin getPredicates Project  projectPullUpPredicates is %s\n",
            projectPullUpPredicates.toString());
    return RelOptPredicateList.of(projectPullUpPredicates);
  }

  /** Infers predicates for a {@link org.apache.calcite.rel.core.Join}. */
  public RelOptPredicateList getPredicates(Join join, RelMetadataQuery mq) {
    RexBuilder rB = join.getCluster().getRexBuilder();
    RelNode left = join.getInput(0);
    RelNode right = join.getInput(1);
    System.out.printf("edwin getPredicates Project Join left is %s, class is %s \n",
            (left instanceof HepRelVertex)?((HepRelVertex) left).getCurrentRel().toString():left.toString(),
            (left instanceof HepRelVertex)?((HepRelVertex) left).getCurrentRel().getClass():left.getClass());

    System.out.printf("edwin getPredicates Project Join right is %s, class is %s \n",
            (left instanceof HepRelVertex)?((HepRelVertex) right).getCurrentRel().toString():right.toString(),
            (left instanceof HepRelVertex)?((HepRelVertex) right).getCurrentRel().getClass():right.getClass());

    final RelOptPredicateList leftInfo = mq.getPulledUpPredicates(left);
    final RelOptPredicateList rightInfo = mq.getPulledUpPredicates(right);

    System.out.printf("edwin getPredicates Project Join leftInfo is %s \n edwin getPredicates Project Join rightInfo is %s \n",
            leftInfo.pulledUpPredicates.toString(), rightInfo.pulledUpPredicates.toString());

    RexNode leftNew = RexUtil.composeConjunction(rB, leftInfo.pulledUpPredicates, false);
    RexNode rightNew = RexUtil.composeConjunction(rB, rightInfo.pulledUpPredicates, false);

    System.out.printf("edwin getPredicates Project Join leftNew is %s, class is %s, operator is %s\n " +
                    "edwin getPredicates Project Join rightNew is %s, calss is %s, operator is %s \n",
            leftNew.toString(), leftNew.getClass(), (leftNew instanceof RexCall)?((RexCall) leftNew).getOperator():"not call",
            rightNew.toString(), rightNew.toString(), (rightNew instanceof  RexCall)? ((RexCall) rightNew).getOperator():"not call");
    System.out.printf("edwin getPredicates Project Join leftNew is operands is %s\n, " +
            "edwin getPredicates Project Join rightNew is operands is %s\n",
            (leftNew instanceof RexCall)?((RexCall) leftNew).getOperands():"not call",
            (rightNew instanceof  RexCall)? ((RexCall) rightNew).getOperands():"not call");

    System.out.printf("dwin getPredicates Project Join nFieldsLeft is %s\n", join.getLeft().getRowType().getFieldList());
    System.out.printf("dwin getPredicates Project Join nFieldsRight is %s\n", join.getRight().getRowType().getFieldList());
    System.out.printf("dwin getPredicates Project Join nSysFields is %s\n", join.getSystemFieldList());

    JoinConditionBasedPredicateInference jI =
        new JoinConditionBasedPredicateInference(join,
            RexUtil.composeConjunction(rB, leftInfo.pulledUpPredicates, false),
            RexUtil.composeConjunction(rB, rightInfo.pulledUpPredicates, false));

    return jI.inferPredicates(false);
  }

  /**
   * Infers predicates for an Aggregate.
   *
   * <p>Pulls up predicates that only contains references to columns in the
   * GroupSet. For e.g.
   *
   * <pre>
   * inputPullUpExprs : { a &gt; 7, b + c &lt; 10, a + e = 9}
   * groupSet         : { a, b}
   * pulledUpExprs    : { a &gt; 7}
   * </pre>
   */
  public RelOptPredicateList getPredicates(Aggregate agg, RelMetadataQuery mq) {
    final RelNode input = agg.getInput();

    System.out.printf("edwin getPredicates Aggregate input is %s, class is %s \n",
            (input instanceof HepRelVertex)?((HepRelVertex) input).getCurrentRel().toString():input.toString(),
            (input instanceof HepRelVertex)?((HepRelVertex) input).getCurrentRel().getClass():input.getClass());

    final RelOptPredicateList inputInfo = mq.getPulledUpPredicates(input);
    final List<RexNode> aggPullUpPredicates = new ArrayList<>();

    ImmutableBitSet groupKeys = agg.getGroupSet();
    Mapping m = Mappings.create(MappingType.PARTIAL_FUNCTION,
        input.getRowType().getFieldCount(), agg.getRowType().getFieldCount());

    System.out.printf("edwin getPredicates Aggregate m.soucre is %d, target is %d, agg class is %s \n",
            m.getSourceCount(), m.getTargetCount(), agg.getRowType().getClass());
    int i = 0;
    for (int j : groupKeys) {
      m.set(j, i++);
    }

    for (RexNode r : inputInfo.pulledUpPredicates) {
      ImmutableBitSet rCols = RelOptUtil.InputFinder.bits(r);
      if (!rCols.isEmpty() && groupKeys.contains(rCols)) {
        r = r.accept(new RexPermuteInputsShuttle(m, input));
        aggPullUpPredicates.add(r);
      }
    }

    System.out.printf("edwin getPredicates Aggregate  projectPullUpPredicates is %s\n",
            aggPullUpPredicates.toString());
    return RelOptPredicateList.of(aggPullUpPredicates);
  }

  /**
   * Infers predicates for a Union.
   */
  public RelOptPredicateList getPredicates(Union union, RelMetadataQuery mq) {
    RexBuilder rB = union.getCluster().getRexBuilder();

    Map<String, RexNode> finalPreds = new HashMap<>();
    List<RexNode> finalResidualPreds = new ArrayList<>();
    for (int i = 0; i < union.getInputs().size(); i++) {
      RelNode input = union.getInputs().get(i);
      RelOptPredicateList info = mq.getPulledUpPredicates(input);
      if (info.pulledUpPredicates.isEmpty()) {
        return RelOptPredicateList.EMPTY;
      }
      Map<String, RexNode> preds = new HashMap<>();
      List<RexNode> residualPreds = new ArrayList<>();
      for (RexNode pred : info.pulledUpPredicates) {
        final String predString = pred.toString();
        if (i == 0) {
          preds.put(predString, pred);
          continue;
        }
        if (finalPreds.containsKey(predString)) {
          preds.put(predString, pred);
        } else {
          residualPreds.add(pred);
        }
      }
      // Add new residual preds
      finalResidualPreds.add(RexUtil.composeConjunction(rB, residualPreds, false));
      // Add those that are not part of the final set to residual
      for (Entry<String, RexNode> e : finalPreds.entrySet()) {
        if (!preds.containsKey(e.getKey())) {
          // This node was in previous union inputs, but it is not in this one
          for (int j = 0; j < i; j++) {
            finalResidualPreds.set(j, RexUtil.composeConjunction(rB, Lists.newArrayList(
                    finalResidualPreds.get(j), e.getValue()), false));
          }
        }
      }
      // Final preds
      finalPreds = preds;
    }

    List<RexNode> preds = new ArrayList<>(finalPreds.values());
    RexNode disjPred = RexUtil.composeDisjunction(rB, finalResidualPreds, false);
    if (!disjPred.isAlwaysTrue()) {
      preds.add(disjPred);
    }
    return RelOptPredicateList.of(preds);
  }

  /**
   * Utility to infer predicates from one side of the join that apply on the
   * other side.
   *
   * <p>Contract is:<ul>
   *
   * <li>initialize with a {@link org.apache.calcite.rel.core.Join} and
   * optional predicates applicable on its left and right subtrees.
   *
   * <li>you can
   * then ask it for equivalentPredicate(s) given a predicate.
   *
   * </ul>
   *
   * <p>So for:
   * <ol>
   * <li>'<code>R1(x) join R2(y) on x = y</code>' a call for
   * equivalentPredicates on '<code>x &gt; 7</code>' will return '
   * <code>[y &gt; 7]</code>'
   * <li>'<code>R1(x) join R2(y) on x = y join R3(z) on y = z</code>' a call for
   * equivalentPredicates on the second join '<code>x &gt; 7</code>' will return
   * </ol>
   */
  static class JoinConditionBasedPredicateInference {
    final Join joinRel;
    final boolean isSemiJoin;
    final int nSysFields;
    final int nFieldsLeft;
    final int nFieldsRight;
    final ImmutableBitSet leftFieldsBitSet;
    final ImmutableBitSet rightFieldsBitSet;
    final ImmutableBitSet allFieldsBitSet;
    //记录索引,BitSet中也来记位, $2==$4，会置2位
    //{0={0, 4}, 1={1}, 2={2, 5}, 3={3}, 4={0, 4}, 5={2, 5}, 6={6}}
    SortedMap<Integer, BitSet> equivalence;
    //记录RexNode的摘要，同时记录ImmutableBitSet引用位置
    final Map<String, ImmutableBitSet> exprFields;
    //只是记录左右子句中  预测的RexNode摘要
    final Set<String> allExprsDigests;
    //一开始为空，
    //将condition中的 条件(RexCall)记录在equalityPredicates
    final Set<String> equalityPredicates;
    //预测后的左节点
    final RexNode leftChildPredicates;
    //预测后的右节点
    final RexNode rightChildPredicates;

    public JoinConditionBasedPredicateInference(Join joinRel,
            RexNode lPreds, RexNode rPreds) {
      this(joinRel, joinRel instanceof SemiJoin, lPreds, rPreds);
    }

    private JoinConditionBasedPredicateInference(Join joinRel, boolean isSemiJoin,
        RexNode lPreds, RexNode rPreds) {
      super();
      this.joinRel = joinRel;
      this.isSemiJoin = isSemiJoin;
      nFieldsLeft = joinRel.getLeft().getRowType().getFieldList().size();
      nFieldsRight = joinRel.getRight().getRowType().getFieldList().size();
      nSysFields = joinRel.getSystemFieldList().size();
      //0, 0+4
      leftFieldsBitSet = ImmutableBitSet.range(nSysFields,
          nSysFields + nFieldsLeft);
      //0+4, 0+4+3
      rightFieldsBitSet = ImmutableBitSet.range(nSysFields + nFieldsLeft,
          nSysFields + nFieldsLeft + nFieldsRight);
      //0, 0+4+3
      allFieldsBitSet = ImmutableBitSet.range(0,
          nSysFields + nFieldsLeft + nFieldsRight);

      exprFields = Maps.newHashMap();
      allExprsDigests = new HashSet<>();

      if (lPreds == null) {
        leftChildPredicates = null;
      } else {
        Mappings.TargetMapping leftMapping = Mappings.createShiftMapping(
            nSysFields + nFieldsLeft, nSysFields, 0, nFieldsLeft);

        //更新RexCall中的operands
        leftChildPredicates = lPreds.accept(
            new RexPermuteInputsShuttle(leftMapping, joinRel.getInput(0)));
        System.out.printf("edwin JoinConditionBasedPredicateInference " +
                "leftChildPredicates is %s \n", leftChildPredicates.toString());

        for (RexNode r : RelOptUtil.conjunctions(leftChildPredicates)) {
          exprFields.put(r.toString(), RelOptUtil.InputFinder.bits(r));
          allExprsDigests.add(r.toString());
        }
      }

      System.out.printf("------------------------------ lPreds line\n");

      if (rPreds == null) {
        rightChildPredicates = null;
      } else {
        Mappings.TargetMapping rightMapping = Mappings.createShiftMapping(
            nSysFields + nFieldsLeft + nFieldsRight,
            nSysFields + nFieldsLeft, 0, nFieldsRight);
        rightChildPredicates = rPreds.accept(
            new RexPermuteInputsShuttle(rightMapping, joinRel.getInput(1)));

        System.out.printf("edwin JoinConditionBasedPredicateInference " +
                "rightChildPredicates is %s \n", rightChildPredicates.toString());

        for (RexNode r : RelOptUtil.conjunctions(rightChildPredicates)) {
          exprFields.put(r.toString(), RelOptUtil.InputFinder.bits(r));
          allExprsDigests.add(r.toString());
        }
      }

      System.out.printf("------------------------------ rPreds line\n");


      equivalence = Maps.newTreeMap();
      equalityPredicates = new HashSet<>();
      for (int i = 0; i < nSysFields + nFieldsLeft + nFieldsRight; i++) {
        equivalence.put(i, BitSets.of(i));
      }

      // Only process equivalences found in the join conditions. Processing
      // Equivalences from the left or right side infer predicates that are
      // already present in the Tree below the join.
      RexBuilder rexBuilder = joinRel.getCluster().getRexBuilder();

      RexNode conditionAfterCompose = compose(rexBuilder, ImmutableList.of(joinRel.getCondition()));
      System.out.printf("edwin JoinConditionBasedPredicateInference conditionAfterCompose is %s \n", conditionAfterCompose);

      List<RexNode> exprs =
          RelOptUtil.conjunctions(
              compose(rexBuilder, ImmutableList.of(joinRel.getCondition())));

      System.out.printf("edwin JoinConditionBasedPredicateInference condition exprs is %s \n", exprs.toString());


      final EquivalenceFinder eF = new EquivalenceFinder();

      //妈的 这块代码没用
      //有用，仅仅是transform有用
      //EquivalenceFinder 对RexCall做两件事
      //1 equivalence记录 condition中 相互等值的记录
      //2 将condition中的 条件(RexCall)记录在equalityPredicates
      new ArrayList<>(
          Lists.transform(exprs,
              new Function<RexNode, Void>() {
                public Void apply(RexNode input) {
                  return input.accept(eF);
                }
              }));

      System.out.printf("edwin JoinConditionBasedPredicateInference condition exprs(transform) is %s，equalityPredicates is %s" +
              " \n", exprs.toString(), equalityPredicates.toString());

      System.out.printf("edwin JoinConditionBasedPredicateInference before closure is %s \n", equivalence.toString());
      equivalence = BitSets.closure(equivalence);
      System.out.printf("edwin JoinConditionBasedPredicateInference after closure is %s \n", equivalence.toString());
      System.out.printf("------------------------------ equivalence end line\n");
    }

    /**
     * The PullUp Strategy is sound but not complete.
     * <ol>
     * <li>We only pullUp inferred predicates for now. Pulling up existing
     * predicates causes an explosion of duplicates. The existing predicates are
     * pushed back down as new predicates. Once we have rules to eliminate
     * duplicate Filter conditions, we should pullUp all predicates.
     * <li>For Left Outer: we infer new predicates from the left and set them as
     * applicable on the Right side. No predicates are pulledUp.
     * <li>Right Outer Joins are handled in an analogous manner.
     * <li>For Full Outer Joins no predicates are pulledUp or inferred.
     * </ol>
     */
    public RelOptPredicateList inferPredicates(
        boolean includeEqualityInference) {
      final List<RexNode> inferredPredicates = new ArrayList<>();
      final List<RexNode> nonFieldsPredicates = new ArrayList<>();
      final Set<String> allExprsDigests = new HashSet<>(this.allExprsDigests);
      final JoinRelType joinType = joinRel.getJoinType();
      final List<RexNode> leftPreds = ImmutableList.copyOf(RelOptUtil.conjunctions(leftChildPredicates));
      final List<RexNode> rightPreds = ImmutableList.copyOf(RelOptUtil.conjunctions(rightChildPredicates));
      switch (joinType) {
      case INNER:
      case LEFT:
        infer(leftPreds, allExprsDigests, inferredPredicates,
            nonFieldsPredicates, includeEqualityInference,
            joinType == JoinRelType.LEFT ? rightFieldsBitSet
                : allFieldsBitSet);
        System.out.printf("edwin inferPredicates after left iner, inferredPredicates is %s, nonFieldsPredicates is %s\n ",
                inferredPredicates.toString(), nonFieldsPredicates.toString());
        break;
      }
      switch (joinType) {
      case INNER:
      case RIGHT:
        infer(rightPreds, allExprsDigests, inferredPredicates,
            nonFieldsPredicates, includeEqualityInference,
            joinType == JoinRelType.RIGHT ? leftFieldsBitSet
                : allFieldsBitSet);
        System.out.printf("edwin inferPredicates after right iner, inferredPredicates is %s, nonFieldsPredicates is %s\n ",
                inferredPredicates.toString(), nonFieldsPredicates.toString());
        break;
      }

      System.out.printf("------------------------------ edwin inferPredicates infer end line \n");

      Mappings.TargetMapping rightMapping = Mappings.createShiftMapping(
          nSysFields + nFieldsLeft + nFieldsRight,
          0, nSysFields + nFieldsLeft, nFieldsRight);

      System.out.printf("edwin rightMapping is %s \n", rightMapping.toString());

      final RexPermuteInputsShuttle rightPermute =
          new RexPermuteInputsShuttle(rightMapping, joinRel);

      Mappings.TargetMapping leftMapping = Mappings.createShiftMapping(
          nSysFields + nFieldsLeft, 0, nSysFields, nFieldsLeft);
      System.out.printf("edwin leftMapping is %s \n", leftMapping.toString());


      final RexPermuteInputsShuttle leftPermute =
          new RexPermuteInputsShuttle(leftMapping, joinRel);
      final List<RexNode> leftInferredPredicates = new ArrayList<>();
      final List<RexNode> rightInferredPredicates = new ArrayList<>();

      for (RexNode iP : inferredPredicates) {
        ImmutableBitSet iPBitSet = RelOptUtil.InputFinder.bits(iP);
        if (leftFieldsBitSet.contains(iPBitSet)) {
          leftInferredPredicates.add(iP.accept(leftPermute));
        } else if (rightFieldsBitSet.contains(iPBitSet)) {
          rightInferredPredicates.add(iP.accept(rightPermute));
        }
      }

      System.out.printf("edwin inferPredicates leftInferredPredicates is %s \n", leftInferredPredicates.toString());
        System.out.printf("edwin inferPredicates rightInferredPredicates is %s \n", rightInferredPredicates.toString());


        if (joinType == JoinRelType.INNER && !nonFieldsPredicates.isEmpty()) {
        // Predicates without field references can be pushed to both inputs
        final Set<String> leftPredsSet = new HashSet<String>(
                Lists.transform(leftPreds, HiveCalciteUtil.REX_STR_FN));
        final Set<String> rightPredsSet = new HashSet<String>(
                Lists.transform(rightPreds, HiveCalciteUtil.REX_STR_FN));
        for (RexNode iP : nonFieldsPredicates) {
          if (!leftPredsSet.contains(iP.toString())) {
            leftInferredPredicates.add(iP);
          }
          if (!rightPredsSet.contains(iP.toString())) {
            rightInferredPredicates.add(iP);
          }
        }
      }

      switch (joinType) {
      case INNER:
        Iterable<RexNode> pulledUpPredicates;
        if (isSemiJoin) {
          pulledUpPredicates = Iterables.concat(leftPreds, leftInferredPredicates);
        } else {
          pulledUpPredicates = Iterables.concat(leftPreds, rightPreds,
                RelOptUtil.conjunctions(joinRel.getCondition()), inferredPredicates);
        }
        return RelOptPredicateList.of(
          pulledUpPredicates, leftInferredPredicates, rightInferredPredicates);
      case LEFT:    
        return RelOptPredicateList.of(    
          leftPreds, EMPTY_LIST, rightInferredPredicates);
      case RIGHT:   
        return RelOptPredicateList.of(    
          rightPreds, leftInferredPredicates, EMPTY_LIST);
      default:
        assert inferredPredicates.size() == 0;
        return RelOptPredicateList.EMPTY;
      }
    }

    public RexNode left() {
      return leftChildPredicates;
    }

    public RexNode right() {
      return rightChildPredicates;
    }

    private void infer(List<RexNode> predicates, Set<String> allExprsDigests,
        List<RexNode> inferedPredicates, List<RexNode> nonFieldsPredicates,
        boolean includeEqualityInference, ImmutableBitSet inferringFields) {
      for (RexNode r : predicates) {
        if (!includeEqualityInference
            && equalityPredicates.contains(r.toString())) {
          continue;
        }
        Iterable<Mapping> ms = mappings(r);
        //System.out.printf("------------edwin JoinConditionBasedPredicateInference mappings-------------- \n");
        if (ms.iterator().hasNext()) {
          //System.out.printf("edwin JoinConditionBasedPredicateInference infer ms is %s \n", ms.i);
          System.out.printf("############################### \n");
          for (Mapping m : ms) {
            System.out.printf("edwin JoinConditionBasedPredicateInference infer m is %s \n", m.toString());
            RexNode tr = r.accept(
                new RexPermuteInputsShuttle(m, joinRel.getInput(0),
                    joinRel.getInput(1)));
            System.out.printf("edwin JoinConditionBasedPredicateInference infer tr is %s, " +
                    "class is %s; %b, %b ,%b\n", tr.toString(), tr.getClass(), inferringFields.contains(RelOptUtil.InputFinder.bits(tr)),
                    allExprsDigests.contains(tr.toString()), isAlwaysTrue(tr));
            if (inferringFields.contains(RelOptUtil.InputFinder.bits(tr))
                && !allExprsDigests.contains(tr.toString())
                && !isAlwaysTrue(tr)) {
              inferedPredicates.add(tr);
              allExprsDigests.add(tr.toString());
            }
          }
        } else {
          if (!isAlwaysTrue(r)) {
            nonFieldsPredicates.add(r);
          }
        }
      }
    }

    Iterable<Mapping> mappings(final RexNode predicate) {
      return new Iterable<Mapping>() {
        public Iterator<Mapping> iterator() {
          ImmutableBitSet fields = exprFields.get(predicate.toString());
          if (fields.cardinality() == 0) {
            return Iterators.emptyIterator();
          }
          System.out.printf("edwin JoinConditionBasedPredicateInference mappings RexNode is %s, fields is %s, cardinality:%s\n",
                  predicate.toString(), fields.toString(), fields.cardinality());
          return new ExprsItr(fields);
        }
      };
    }

    private void equivalent(int p1, int p2) {
      BitSet b = equivalence.get(p1);
      b.set(p2);

      b = equivalence.get(p2);
      b.set(p1);
    }

    RexNode compose(RexBuilder rexBuilder, Iterable<RexNode> exprs) {
      exprs = Linq4j.asEnumerable(exprs).where(new Predicate1<RexNode>() {
        public boolean apply(RexNode expr) {
          return expr != null;
        }
      });
      return RexUtil.composeConjunction(rexBuilder, exprs, false);
    }

    /**
     * Find expressions of the form 'col_x = col_y'.
     */
    class EquivalenceFinder extends RexVisitorImpl<Void> {
      protected EquivalenceFinder() {
        super(true);
      }

      @Override public Void visitCall(RexCall call) {
        if (call.getOperator().getKind() == SqlKind.EQUALS) {
          int lPos = pos(call.getOperands().get(0));
          int rPos = pos(call.getOperands().get(1));
          if (lPos != -1 && rPos != -1) {
            JoinConditionBasedPredicateInference.this.equivalent(lPos, rPos);
            JoinConditionBasedPredicateInference.this.equalityPredicates
                .add(call.toString());
          }
        }
        return null;
      }
    }

    /**
     * Given an expression returns all the possible substitutions.
     *
     * <p>For example, for an expression 'a + b + c' and the following
     * equivalences: <pre>
     * a : {a, b}
     * b : {a, b}
     * c : {c, e}
     * </pre>
     *
     * <p>The following Mappings will be returned:
     * <pre>
     * {a &rarr; a, b &rarr; a, c &rarr; c}
     * {a &rarr; a, b &rarr; a, c &rarr; e}
     * {a &rarr; a, b &rarr; b, c &rarr; c}
     * {a &rarr; a, b &rarr; b, c &rarr; e}
     * {a &rarr; b, b &rarr; a, c &rarr; c}
     * {a &rarr; b, b &rarr; a, c &rarr; e}
     * {a &rarr; b, b &rarr; b, c &rarr; c}
     * {a &rarr; b, b &rarr; b, c &rarr; e}
     * </pre>
     *
     * <p>which imply the following inferences:
     * <pre>
     * a + a + c
     * a + a + e
     * a + b + c
     * a + b + e
     * b + a + c
     * b + a + e
     * b + b + c
     * b + b + e
     * </pre>
     */
    class ExprsItr implements Iterator<Mapping> {
      final int[] columns;
      final BitSet[] columnSets;
      final int[] iterationIdx;
      Mapping nextMapping;
      boolean firstCall;

      ExprsItr(ImmutableBitSet fields) {
        nextMapping = null;
        columns = new int[fields.cardinality()];
        columnSets = new BitSet[fields.cardinality()];
        iterationIdx = new int[fields.cardinality()];
        for (int j = 0, i = fields.nextSetBit(0); i >= 0; i = fields
            .nextSetBit(i + 1), j++) {
          columns[j] = i;
          columnSets[j] = equivalence.get(i);
          System.out.printf("edwin JoinConditionBasedPredicateInference ExprsItr columnSets[j] is %s \n",
                  columnSets[j].toString());
          iterationIdx[j] = 0;
        }
        firstCall = true;
      }

      public boolean hasNext() {
        if (firstCall) {
          initializeMapping();
          firstCall = false;
        } else {
          computeNextMapping(iterationIdx.length - 1);
        }
        return nextMapping != null;
      }

      public Mapping next() {
        return nextMapping;
      }

      public void remove() {
        throw new UnsupportedOperationException();
      }

      private void computeNextMapping(int level) {
        int t = columnSets[level].nextSetBit(iterationIdx[level]);
        if (t < 0) {
          if (level == 0) {
            nextMapping = null;
          } else {
            iterationIdx[level] = 0;
            computeNextMapping(level - 1);
          }
        } else {
          nextMapping.set(columns[level], t);
          iterationIdx[level] = t + 1;
        }
      }

      private void initializeMapping() {
        nextMapping = Mappings.create(MappingType.PARTIAL_FUNCTION,
            nSysFields + nFieldsLeft + nFieldsRight,
            nSysFields + nFieldsLeft + nFieldsRight);
        for (int i = 0; i < columnSets.length; i++) {
          BitSet c = columnSets[i];
          int t = c.nextSetBit(iterationIdx[i]);
          if (t < 0) {
            nextMapping = null;
            return;
          }
          //0 0
          //2 2
          nextMapping.set(columns[i], t);
          iterationIdx[i] = t + 1;
        }
      }
    }

    private int pos(RexNode expr) {
      if (expr instanceof RexInputRef) {
        return ((RexInputRef) expr).getIndex();
      }
      return -1;
    }

    private boolean isAlwaysTrue(RexNode predicate) {
      if (predicate instanceof RexCall) {
        RexCall c = (RexCall) predicate;
        if (c.getOperator().getKind() == SqlKind.EQUALS) {
          int lPos = pos(c.getOperands().get(0));
          int rPos = pos(c.getOperands().get(1));
          return lPos != -1 && lPos == rPos;
        }
      }
      return predicate.isAlwaysTrue();
    }
  }

}
