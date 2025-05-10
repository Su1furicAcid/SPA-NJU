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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.*;

import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.canHoldInt;
import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.evaluate;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        // 1.
        for (Stmt stmt : icfg.getNodes()) {
            if (stmt instanceof StoreField storeField) {
                if (storeField.isStatic()) {
                    JField field = storeField.getFieldRef().resolve();
                    Set<StoreField> stores = staticFieldStores.getOrDefault(field, new HashSet<>());
                    stores.add(storeField);
                    staticFieldStores.put(field, stores);
                }
            }
            if (stmt instanceof LoadField loadField) {
                if (loadField.isStatic()) {
                    JField field = loadField.getFieldRef().resolve();
                    Set<LoadField> loads = staticFieldLoads.getOrDefault(field, new HashSet<>());
                    loads.add(loadField);
                    staticFieldLoads.put(field, loads);
                }
            }
        }
        // 2.
        Collection<Var> vars = pta.getVars();
        Map<Obj, Set<Var>> objToVars = new HashMap<>();
        for (Var var : vars) {
            Set<Obj> objs = pta.getPointsToSet(var);
            for (Obj obj : objs) {
                objToVars.computeIfAbsent(obj, k -> new HashSet<>()).add(var);
            }
        }
        for (Var var : vars) {
            Set<Var> aliasSet = new HashSet<>();
            Set<Obj> objs = pta.getPointsToSet(var);
            for (Obj obj : objs) {
                aliasSet.addAll(objToVars.getOrDefault(obj, Collections.emptySet()));
            }
            aliasSets.put(var, aliasSet);
        }
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // Do not need to change
        return out.copyFrom(in);
    }

    private final Map<JField, Set<LoadField>> staticFieldLoads = new HashMap<>();
    private final Map<JField, Set<StoreField>> staticFieldStores = new HashMap<>();
    private final Map<Var, Set<Var>> aliasSets = new HashMap<>();

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // a.f = x
        if (stmt instanceof StoreField storeFieldStmt) {
            if (storeFieldStmt.isStatic()) {
                if (canHoldInt(storeFieldStmt.getRValue())) {
                    JField field = storeFieldStmt.getFieldRef().resolve();
                    Set<LoadField> loads = staticFieldLoads.getOrDefault(field, new HashSet<>());
                    for (LoadField load : loads) {
                        solver.addToWorkList(load);
                    }
                }
            } else {
                if (canHoldInt(storeFieldStmt.getRValue())) {
                    Var base = ((InstanceFieldAccess)storeFieldStmt.getFieldAccess()).getBase();
                    Set<Var> aliasBase = aliasSets.getOrDefault(base, new HashSet<>());
                    JField storeField = storeFieldStmt.getFieldRef().resolve();
                    for (Var alias : aliasBase) {
                        for (LoadField loadFieldStmt : alias.getLoadFields()) {
                            JField loadField = loadFieldStmt.getFieldRef().resolve();
                            if (storeField.equals(loadField)) {
                                solver.addToWorkList(loadFieldStmt);
                            }
                        }
                    }
                }
            }
            return out.copyFrom(in);
        }
        // x = a.f
        if (stmt instanceof LoadField loadFieldStmt) {
            CPFact newOut = in.copy();
            if (loadFieldStmt.isStatic()) {
                if (canHoldInt(loadFieldStmt.getLValue())) {
                    // static field x = T.f
                    // Do not need to consider alias of static field
                    // Find all T.f = y
                    JField loadField = loadFieldStmt.getFieldRef().resolve();
                    Value loadValue = Value.getUndef();
                    Set<StoreField> stores = staticFieldStores.getOrDefault(loadField, new HashSet<>());
                    for (StoreField store : stores) {
                        JField storeField = store.getFieldRef().resolve();
                        if (loadField.equals(storeField)) {
                            // T.f = y
                            CPFact storeIn = solver.getInFact(store);
                            Value storeValue = evaluate(store.getRValue(), storeIn);
                            loadValue = cp.meetValue(loadValue, storeValue);
                        }
                    }
                    newOut.update(loadFieldStmt.getLValue(), loadValue);
                }
            } else {
                if (canHoldInt(loadFieldStmt.getLValue())) {
                    // instance field x = y.f
                    // Consider alias of y
                    JField loadField = loadFieldStmt.getFieldRef().resolve();
                    Value loadValue = Value.getUndef();
                    Var y = ((InstanceFieldAccess) loadFieldStmt.getRValue()).getBase();
                    Set<Var> aliasY = aliasSets.getOrDefault(y, new HashSet<>());
                    for (Var alias : aliasY) {
                        for (StoreField store : alias.getStoreFields()) {
                            JField storeField = store.getFieldRef().resolve();
                            if (loadField.equals(storeField)) {
                                // for all alias, y.f = z
                                CPFact storeIn = solver.getInFact(store);
                                Value storeValue = evaluate(store.getRValue(), storeIn);
                                loadValue = cp.meetValue(loadValue, storeValue);
                            }
                        }
                    }
                    newOut.update(loadFieldStmt.getLValue(), loadValue);
                }
            }
            return out.copyFrom(newOut);
        }
        // x = a[i]
        if (stmt instanceof LoadArray loadArray) {
            CPFact newOut = in.copy();
            if (canHoldInt(loadArray.getLValue())) {
                Value loadValue = Value.getUndef();
                ArrayAccess loadArrayAccess = loadArray.getArrayAccess();
                Var index = loadArrayAccess.getIndex();
                Value iVal = in.get(index);
                Var a = loadArrayAccess.getBase();
                Set<Var> aliasA = aliasSets.getOrDefault(a, new HashSet<>());
                for (Var alias : aliasA) {
                    for (StoreArray storeArray : alias.getStoreArrays()) {
                        ArrayAccess storeArrayAccess = storeArray.getArrayAccess();
                        Var jndex = storeArrayAccess.getIndex();
                        CPFact storeIn = solver.getInFact(storeArray);
                        Value jVal = storeIn.get(jndex);
                        // a[i] and b[j]
                        if (iVal.isUndef() || jVal.isUndef()) {
                            continue;
                        }
                        if (iVal.isConstant() && jVal.isConstant() && !iVal.equals(jVal)) {
                            continue;
                        }
                        Value storeValue = evaluate(storeArray.getRValue(), storeIn);
                        loadValue = cp.meetValue(loadValue, storeValue);
                    }
                }
                newOut.update(loadArray.getLValue(), loadValue);
            }
            return out.copyFrom(newOut);
        }
        // Other
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        Invoke invoke = (Invoke) edge.getSource();
        CPFact newOut = out.copy();
        // x = m(...) or m(...)
        Var LHS = invoke.getLValue();
        if (LHS != null) {
            newOut.remove(LHS);
        }
        return newOut;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        Invoke source = (Invoke) edge.getSource();
        InvokeExp RHS = source.getRValue();
        CPFact out = new CPFact();
        JMethod method = edge.getCallee();
        if (method != null) {
            IR methodIR = method.getIR();
            int argCount = RHS.getArgCount();
            for (int i = 0; i < argCount; i++) {
                Var arg = RHS.getArg(i);
                Value argVal = callSiteOut.get(arg);
                if (argVal != null) {
                    Var param = methodIR.getParam(i);
                    out.update(param, argVal);
                }
            }
        }
        return out;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact out = new CPFact();
        Invoke callSite = (Invoke) edge.getCallSite();
        Var LHS = callSite.getLValue();
        if (LHS != null) {
            Value finalVal = Value.getUndef();
            Collection<Var> retVars = edge.getReturnVars();
            for (Var retVar : retVars) {
                Value retVarVal = returnOut.get(retVar);
                finalVal = cp.meetValue(finalVal, retVarVal);
            }
            out.update(LHS, finalVal);
        }
        return out;
    }
}
