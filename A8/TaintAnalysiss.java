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

package pascal.taie.analysis.pta.plugin.taint;

import heros.flowfunc.Transfer;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        result.getCSCallGraph().edges().forEach(edge -> {
            CSCallSite csCallSite = edge.getCallSite();
            CSMethod csMethod = edge.getCallee();
            Context context = csCallSite.getContext();
            JMethod method = csMethod.getMethod();
            Invoke invoke = csCallSite.getCallSite();
            int index = isSink(method);
            if (index != -100) {
                Var ai = invoke.getInvokeExp().getArg(index);
                CSVar cxtAi = csManager.getCSVar(context, ai);
                PointsToSet aiPts = cxtAi.getPointsToSet();
                for (CSObj cxtAiObj : aiPts.getObjects()) {
                    Obj aiObj = cxtAiObj.getObject();
                    if (manager.isTaint(aiObj)) {
                        Invoke sourceCall = manager.getSourceCall(aiObj);
                        taintFlows.add(new TaintFlow(sourceCall, invoke, index));
                    }
                }
            }
        });
        return taintFlows;
    }

    public Type isSource(JMethod method) {
        Set<Source> sources = config.getSources();
        for (Source source : sources) {
            if (source.method().equals(method)) {
                return source.type();
            }
        }
        return null;
    }

    public int isSink(JMethod method) {
        Set<Sink> sinks = config.getSinks();
        for (Sink sink : sinks) {
            if (sink.method().equals(method)) {
                return sink.index();
            }
        }
        return -100;
    }

    public Obj makeTaintObj(Invoke invoke, Type type) {
        return manager.makeTaint(invoke, type);
    }

    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }

    public Invoke getSourceCall(Obj obj) {
        return manager.getSourceCall(obj);
    }

    public void doTaintTransfer(Invoke invoke, JMethod callee, Context context, CSVar cxtRecv) {
        Set<TaintTransfer> taintTransfers = config.getTransfers();
        for (TaintTransfer taintTransfer : taintTransfers) {
            if (taintTransfer.method().equals(callee)) {
                int from = taintTransfer.from();
                int to = taintTransfer.to();
                if (from >= 0 && to == TaintTransfer.RESULT) {
                    // arg-to-result
                    // r = x.k(a1, ..., an)
                    Var varR = invoke.getLValue();
                    if (varR != null) {
                        CSVar cxtVarR = csManager.getCSVar(context, varR);
                        Var ai = invoke.getInvokeExp().getArg(from);
                        CSVar cxtAi = csManager.getCSVar(context, ai);
                        Type newType = taintTransfer.type();
                        solver.addTFGEdge(cxtAi, cxtVarR, newType);
                    }
                }
                if (!invoke.isStatic()) {
                    if (from == -1) {
                        // base-to-result
                        // r = x.k(a1, ..., an)
                        Var varR = invoke.getLValue();
                        if (varR != null) {
                            CSVar cxtVarR = csManager.getCSVar(context, varR);
                            Type newType = taintTransfer.type();
                            solver.addTFGEdge(cxtRecv, cxtVarR, newType);
                        }
                    }
                    if (from >= 0 && to == TaintTransfer.BASE) {
                        // arg-to-base
                        // r = x.k(a1, ..., an)
                        Var ai = invoke.getInvokeExp().getArg(from);
                        CSVar cxtAi = csManager.getCSVar(context, ai);
                        Type newType = taintTransfer.type();
                        solver.addTFGEdge(cxtAi, cxtRecv, newType);
                    }
                }
            }
        }
    }
}
