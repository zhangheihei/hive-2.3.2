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
package org.apache.hadoop.hive.ql.optimizer.calcite.rules;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.calcite.plan.RelOptRule;
import org.apache.calcite.plan.RelOptRuleCall;
import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.Filter;
import org.apache.calcite.rel.core.Project;
import org.apache.calcite.rex.RexBuilder;
import org.apache.calcite.rex.RexCall;
import org.apache.calcite.rex.RexInputRef;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.rex.RexShuttle;
import org.apache.calcite.rex.RexUtil;
import org.apache.calcite.tools.RelBuilder;
import org.apache.calcite.tools.RelBuilderFactory;
import org.apache.hadoop.hive.ql.optimizer.calcite.HiveCalciteUtil;
import org.apache.hadoop.hive.ql.optimizer.calcite.HiveRelFactories;
import org.apache.hadoop.hive.ql.optimizer.calcite.reloperators.HiveFilter;
import org.apache.hadoop.hive.ql.optimizer.calcite.reloperators.HiveProject;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.common.collect.Lists;

import static org.apache.calcite.sql.SqlKind.EQUALS;

/**
 * Planner rule that infers constant expressions from Filter into
 * a Project operator.
 */
//就where语句中的常量，扫描到Project中
public class HiveProjectFilterPullUpConstantsRule extends RelOptRule {

  protected static final Logger LOG = LoggerFactory.getLogger(
          HiveProjectFilterPullUpConstantsRule.class);

  public static final HiveProjectFilterPullUpConstantsRule INSTANCE =
          new HiveProjectFilterPullUpConstantsRule(HiveProject.class, HiveFilter.class,
                  HiveRelFactories.HIVE_BUILDER);

  public HiveProjectFilterPullUpConstantsRule(
      Class<? extends Project> projectClass,
      Class<? extends Filter> filterClass,
      RelBuilderFactory relBuilderFactory) {
    super(operand(projectClass,
            operand(filterClass, any())),
            relBuilderFactory, null);
  }

  @Override
  public boolean matches(RelOptRuleCall call) {
      //取filter关系
    final Filter filterRel = call.rel(1);
    //---------------------------------------------------
      System.out.printf("edwin HiveProjectFilterPullUpConstantsRule matches condition is %s, class is %s, kind is %s \n",
              filterRel.getCondition().toString(), filterRel.getCondition().getClass(),
              filterRel.getCondition().getKind());
    final List<RexNode> conjunctions = RelOptUtil.conjunctions(filterRel.getCondition());
    for (RexNode conjunction: conjunctions) {
      if (((RexCall)conjunction).getOperator().getKind() == EQUALS){
        System.out.printf("edwin HiveProjectFilterPullUpConstantsRule matches condition " +
                "conjunction is %s, operands0 is %s, operands0 class is %s, operands1 is %s, operands1 class is %s \n",
                conjunction.toString(), ((RexCall) conjunction).operands.get(0).toString(), ((RexCall) conjunction).operands.get(0).getClass(),
                ((RexCall) conjunction).operands.get(1).toString(), ((RexCall) conjunction).operands.get(1).getClass());
      }
    }
    //---------------------------------------------------
    RexNode condition = filterRel.getCondition();
    if (!HiveCalciteUtil.isDeterministic(condition)) {
      System.out.printf("edwin HiveProjectFilterPullUpConstantsRule matches is false \n");
      return false;
    }
    System.out.printf("edwin HiveProjectFilterPullUpConstantsRule matches is true \n");
    return super.matches(call);
  }

  public void onMatch(RelOptRuleCall call) {
    final Project project = call.rel(0);
    final Filter filter = call.rel(1);
    final RelBuilder builder = call.builder();

    List<RexNode> projects = project.getChildExps();
    for (RexNode node : projects) {
      System.out.printf("edwin HiveProjectFilterPullUpConstantsRule onMatch " +
              "project is %s, class is %s \n", node.toString(), node.getClass());
    }

    List<RexNode> newProjects = rewriteProjects(projects, filter.getCondition(), builder);
    if (newProjects == null) {
      System.out.printf("edwin HiveProjectFilterPullUpConstantsRule onMatch nothing to do \n");
      return;
    }

    System.out.printf("edwin HiveProjectFilterPullUpConstantsRule transformTo, " +
            "FieldNames is %s \n", project.getRowType().getFieldNames());
    RelNode newProjRel = builder.push(filter)
            .project(newProjects, project.getRowType().getFieldNames()).build();
    call.transformTo(newProjRel);
  }

  // Rewrite projects to replace column references by constants when possible
  @SuppressWarnings("incomplete-switch")
  private static List<RexNode> rewriteProjects(List<RexNode> projects,
          RexNode newPushedCondition, RelBuilder relBuilder) {
    final List<RexNode> conjunctions = RelOptUtil.conjunctions(newPushedCondition);
    final Map<String, RexNode> conditions = new HashMap<String, RexNode>();
    for (RexNode conjunction: conjunctions) {
      // 1.1. If it is not a RexCall, we continue
      if (!(conjunction instanceof RexCall)) {
        continue;
      }
      // 1.2. We extract the information that we need
      RexCall conjCall = (RexCall) conjunction;
      switch (conjCall.getOperator().getKind()) {
        case EQUALS:
          if (!(RexUtil.isConstant(conjCall.operands.get(0))) &&
                  RexUtil.isConstant(conjCall.operands.get(1))) {
            conditions.put(conjCall.operands.get(0).toString(), conjCall.operands.get(1));
          } else if (!(RexUtil.isConstant(conjCall.operands.get(1))) &&
                  RexUtil.isConstant(conjCall.operands.get(0))) {
            conditions.put(conjCall.operands.get(1).toString(), conjCall.operands.get(0));
          }
          break;
        case IS_NULL:
          conditions.put(conjCall.operands.get(0).toString(),
                  relBuilder.getRexBuilder().makeNullLiteral(
                          conjCall.operands.get(0).getType().getSqlTypeName()));
      }
    }

    RexReplacer replacer = new RexReplacer(relBuilder.getRexBuilder(), conditions);
    List<RexNode> newProjects = Lists.newArrayList(projects);
    replacer.mutate(newProjects);
    if (replacer.replaced) {
      return newProjects;
    }
    return null;
  }

  protected static class RexReplacer extends RexShuttle {
    private final RexBuilder rexBuilder;
    private final Map<String, RexNode> replacements;
    private boolean replaced;

    RexReplacer(
        RexBuilder rexBuilder,
        Map<String, RexNode> replacements) {
      this.rexBuilder = rexBuilder;
      this.replacements = replacements;
      this.replaced = false;
    }

    @Override public RexNode visitInputRef(RexInputRef inputRef) {
      RexNode node = visit(inputRef);
      if (node == null) {
        return super.visitInputRef(inputRef);
      }
      this.replaced = true;
      return node;
    }

    @Override public RexNode visitCall(RexCall call) {
      RexNode node = visit(call);
      if (node != null) {
        this.replaced = true;
        return node;
      }
      return super.visitCall(call);
    }

    //目的是替换常量,将where语句中已经的常量
    //替换到project字段中
    private RexNode visit(final RexNode call) {
      RexNode replacement = replacements.get(call.toString());
      if (replacement == null) {
        return null;
      }

      System.out.printf("edwin RexReplacer replacement is %s, type is %s, class is %s, " +
              "call is %s, type is %s, class is %s \n", replacement.toString(), replacement.getType().toString(),
              replacement.getType().getClass(), call.toString(), call.getType().toString(), call.getType().getClass());
      if (replacement.getType().equals(call.getType())) {
        return replacement;
      }
      return rexBuilder.makeCast(call.getType(), replacement, true);
    }
  }
}