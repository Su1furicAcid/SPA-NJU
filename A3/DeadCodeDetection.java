/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        DataflowResult<Stmt, CPFact> constants = ir.getResult(ConstantPropagation.ID);
        DataflowResult<Stmt, SetFact<Var>> liveVars = ir.getResult(LiveVariableAnalysis.ID);

        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Set<Stmt> reachable = new HashSet<>();
        Queue<Stmt> queue = new LinkedList<>();
        queue.add(cfg.getEntry());

        while (!queue.isEmpty()) {
            Stmt stmt = queue.poll();
            if (!reachable.add(stmt)) continue;

            // Handle dead assignment
            if (stmt instanceof AssignStmt<?, ?> assign) {
                LValue lhs = assign.getLValue();
                RValue rhs = assign.getRValue();
                if (hasNoSideEffect(rhs) && lhs instanceof Var var) {
                    SetFact<Var> out = liveVars.getOutFact(assign);
                    if (!out.contains(var)) {
                        deadCode.add(assign);
                    }
                }
            }

            // Handle If
            if (stmt instanceof If ifStmt) {
                CPFact in = constants.getInFact(ifStmt);
                Value cond = ConstantPropagation.evaluate(ifStmt.getCondition(), in);

                for (Edge<Stmt> edge : cfg.getOutEdgesOf(ifStmt)) {
                    Edge.Kind kind = edge.getKind();
                    boolean follow = false;

                    if (!cond.isConstant()) {
                        // NAC or Undef: conservatively follow all outgoing edges
                        follow = true;
                    } else {
                        int val = cond.getConstant();
                        follow = (kind == Edge.Kind.IF_TRUE && val != 0)
                                || (kind == Edge.Kind.IF_FALSE && val == 0)
                                || (kind != Edge.Kind.IF_TRUE && kind != Edge.Kind.IF_FALSE);
                    }

                    if (follow) {
                        queue.add(edge.getTarget());
                    }
                }
                continue;
            }

            // Handle Switch
            if (stmt instanceof SwitchStmt switchStmt) {
                CPFact in = constants.getInFact(switchStmt);
                Value cond = ConstantPropagation.evaluate(switchStmt.getVar(), in);
                boolean matchedCase = false;

                for (Edge<Stmt> edge : cfg.getOutEdgesOf(switchStmt)) {
                    Edge.Kind kind = edge.getKind();
                    if (!cond.isConstant()) {
                        // NAC or Undef: follow all edges
                        queue.add(edge.getTarget());
                    } else {
                        int val = cond.getConstant();
                        if (kind == Edge.Kind.SWITCH_CASE && edge.getCaseValue() == val) {
                            queue.add(edge.getTarget());
                            matchedCase = true;
                        } else if (kind != Edge.Kind.SWITCH_CASE && kind != Edge.Kind.SWITCH_DEFAULT) {
                            queue.add(edge.getTarget());
                        }
                    }
                }

                // If no constant match and cond is constant, follow default
                if (cond.isConstant() && !matchedCase) {
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(switchStmt)) {
                        if (edge.getKind() == Edge.Kind.SWITCH_DEFAULT) {
                            queue.add(edge.getTarget());
                        }
                    }
                }
                continue;
            }

            // Default: enqueue all successors
            for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                queue.add(edge.getTarget());
            }
        }

        // Merge: collect unreachable statements
        for (Stmt stmt : cfg.getNodes()) {
            if (!reachable.contains(stmt) && !cfg.isEntry(stmt) && !cfg.isExit(stmt)) {
                deadCode.add(stmt);
            }
        }

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
