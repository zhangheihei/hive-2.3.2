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

package org.apache.hadoop.hive.ql.lib;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;
import org.apache.hadoop.hive.ql.parse.ASTNode;

import org.apache.hadoop.hive.ql.parse.ASTNodeOrigin;
import org.apache.hadoop.hive.ql.parse.SemanticException;
import org.apache.hadoop.hive.ql.plan.ExprNodeDesc;

/**
 * base class for operator graph walker this class takes list of starting ops
 * and walks them one by one. it maintains list of walked operators
 * (dispatchedList) and a list of operators that are discovered but not yet
 * dispatched
 */
public class DefaultGraphWalker implements GraphWalker {

  /**
   * opStack keeps the nodes that have been visited, but have not been
   * dispatched yet
   */
  //保存还没dispatch的节点
  protected final Stack<Node> opStack;
  /**
   * opQueue keeps the nodes in the order that the were dispatched.
   * Then it is used to go through the processed nodes and store
   * the results that the dispatcher has produced (if any)
   */
  //按顺序保存已经dispatch的节点
  protected final Queue<Node> opQueue;
  /**
   * toWalk stores the starting nodes for the graph that needs to be
   * traversed
   */
  protected final List<Node> toWalk = new ArrayList<Node>();
  //walk graph:每个节点NODE 丰富为ExprDesc;dispatch过的节点
  protected final IdentityHashMap<Node, Object> retMap = new  IdentityHashMap<Node, Object>();
  protected final Dispatcher dispatcher;

  /**
   * Constructor.
   *
   * @param disp
   *          dispatcher to call for each op encountered
   */
  public DefaultGraphWalker(Dispatcher disp) {
    dispatcher = disp;
    opStack = new Stack<Node>();
    opQueue = new LinkedList<Node>();
  }

  /**
   * @return the doneList
   */
  protected Set<Node> getDispatchedList() {
    return retMap.keySet();
  }

  /**
   * Dispatch the current operator.
   *
   * @param nd
   *          node being walked
   * @param ndStack
   *          stack of nodes encountered
   * @throws SemanticException
   */
  /*
  * ndStack:还没dispatch的节点
  * */
  public void dispatch(Node nd, Stack<Node> ndStack) throws SemanticException {
    dispatchAndReturn(nd, ndStack);
  }

  /**
   * Returns dispatch result
   */
  public <T> T dispatchAndReturn(Node nd, Stack<Node> ndStack) throws SemanticException {
    Object[] nodeOutputs = null;
    if (nd.getChildren() != null) {
      nodeOutputs = new Object[nd.getChildren().size()];
      int i = 0;
      //nodeOutPut存的是对应节点的desc
      for (Node child : nd.getChildren()) {
        nodeOutputs[i++] = retMap.get(child);
      }
    }

    if (nd instanceof ASTNode) {
      System.out.printf("edwin dispatchAndReturn node is: %s%n", ((ASTNode) nd).toStringTree());

    }

    if (nodeOutputs != null) {
      System.out.printf("edwin DefualtGraphWalker dispatchAndReturn progress %d%n",nodeOutputs.length);
    }
    //nodeOutputs存放nd的子节点
    Object retVal = dispatcher.dispatch(nd, ndStack, nodeOutputs);
    if (retVal instanceof ExprNodeDesc) {
      System.out.printf("edwin dispatchAndReturn node conver desc  is: %s%n", ((ExprNodeDesc) retVal).toString());
    }

    //每个nd经过处理
    retMap.put(nd, retVal);
    return (T) retVal;
  }

  /**
   * starting point for walking.
   *
   * @throws SemanticException
   */
  /*
  * startNodes:是where表达式节点
  * nodeOutput入参是认为NULL
  * */
  public void startWalking(Collection<Node> startNodes,
      HashMap<Node, Object> nodeOutput) throws SemanticException {
    toWalk.addAll(startNodes);
    while (toWalk.size() > 0) {
      Node nd = toWalk.remove(0);
      if (nd instanceof ASTNode) {
        System.out.printf("edwin DefualtGraphWalker walk start: %s%n", ((ASTNode) nd).toStringTree());

      }

      walk(nd);
      if (nd instanceof ASTNode) {
        System.out.printf("edwin ExpressionWalker walk inner** end: %s%n", ((ASTNode) nd).toStringTree());
        System.out.printf("edwin DefualtGraphWalker walk end: %s%n", ((ASTNode) nd).toStringTree());
      }


      // Some walkers extending DefaultGraphWalker e.g. ForwardWalker
      // do not use opQueue and rely uniquely in the toWalk structure,
      // thus we store the results produced by the dispatcher here
      // TODO: rewriting the logic of those walkers to use opQueue
      if (nodeOutput != null && getDispatchedList().contains(nd)) {
        nodeOutput.put(nd, retMap.get(nd));
      }
    }
    //ForwardWalke不会用opQueue。所以要在上面先把根节点保存在nodeOupput中
    // Store the results produced by the dispatcher
    while (!opQueue.isEmpty()) {
      Node node = opQueue.poll();
      if (nodeOutput != null && getDispatchedList().contains(node)) {
        nodeOutput.put(node, retMap.get(node));
      }
    }
  }

  /**
   * walk the current operator and its descendants.
   *
   * @param nd
   *          current operator in the graph
   * @throws SemanticException
   */
  protected void walk(Node nd) throws SemanticException {
    // Push the node in the stack
    opStack.push(nd);

    if (nd instanceof ASTNode) {
      System.out.printf("edwin DefualtGraphWalker walk inner**: %s%n", ((ASTNode) nd).toStringTree());

    }
    // While there are still nodes to dispatch...
    while (!opStack.empty()) {
      //查看栈顶对象而不移除它
      Node node = opStack.peek();
      System.out.printf("-------------edwin DefualtGraphWalker walk outer progress %d%n",opStack.size());
      //IdentityHashMap<Node, Object>
      if (node.getChildren() == null ||
              getDispatchedList().containsAll(node.getChildren())) {
        // Dispatch current node
        if (!getDispatchedList().contains(node)) {
          System.out.printf("edwin DefualtGraphWalker walk progress %d%n",opStack.size());
          dispatch(node, opStack);
          opQueue.add(node);
        }
        opStack.pop();
        continue;
      }

      // Add a single child and restart the loop
      for (Node childNode : node.getChildren()) {
        if (!getDispatchedList().contains(childNode)) {
          opStack.push(childNode);
          break;
        }
      }
    } // end while
  }

}
