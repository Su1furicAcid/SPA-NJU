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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.apache.logging.log4j.core.appender.ScriptAppenderSelector;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (callGraph.addReachableMethod(method)) {
            List<Stmt> stmts = method.getIR().getStmts();
            // visitor pattern
            for (Stmt stmt : stmts) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            // x = new T();
            Obj as = heapModel.getObj(stmt);
            PointsToSet pts = new PointsToSet(as);
            Pointer pt = pointerFlowGraph.getVarPtr(stmt.getLValue());
            // Add (x, oi) to WL
            workList.addEntry(pt, pts);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            // x = y;
            Pointer ptrX = pointerFlowGraph.getVarPtr(stmt.getLValue());
            Pointer ptrY = pointerFlowGraph.getVarPtr(stmt.getRValue());
            // Add edge y -> x
            addPFGEdge(ptrY, ptrX);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            // y = x.f (static)
            if (stmt.isStatic()) {
                Pointer ptrY = pointerFlowGraph.getVarPtr(stmt.getLValue());
                JField field = stmt.getFieldRef().resolve();
                Pointer ptrXf = pointerFlowGraph.getStaticField(field);
                addPFGEdge(ptrXf, ptrY);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            // x.f = y (static)
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                Pointer ptrXf = pointerFlowGraph.getStaticField(field);
                Pointer ptrY = pointerFlowGraph.getVarPtr(stmt.getRValue());
                addPFGEdge(ptrY, ptrXf);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            // r = T.m(a1, ..., an) (static)
            if (stmt.isStatic()) {
                JMethod method = resolveCallee(null, stmt);
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, method))) {
                    addReachable(method);
                    IR methodIR = method.getIR();
                    // ai -> pi
                    InvokeExp invokeExp = stmt.getInvokeExp();
                    int count = invokeExp.getArgCount();
                    for (int i = 0; i < count; i++) {
                        Var ai = invokeExp.getArg(i);
                        Var pi = methodIR.getParam(i);
                        Pointer ptrAi = pointerFlowGraph.getVarPtr(ai);
                        Pointer ptrPi = pointerFlowGraph.getVarPtr(pi);
                        addPFGEdge(ptrAi, ptrPi);
                    }
                    // ret -> r
                    Var R = stmt.getLValue();
                    if (R != null) {
                        Pointer ptrR = pointerFlowGraph.getVarPtr(R);
                        List<Var> retVars = methodIR.getReturnVars();
                        for (Var retVar : retVars) {
                            Pointer ptrRV = pointerFlowGraph.getVarPtr(retVar);
                            addPFGEdge(ptrRV, ptrR);
                        }
                    }
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer n = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet diffPts = propagate(n, pts);
            if (n instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                for (Obj obj : diffPts) {
                    // x.f = y (instance)
                    for (StoreField storeField : var.getStoreFields()) {
                        Var y = storeField.getRValue();
                        Pointer ptrY = pointerFlowGraph.getVarPtr(y);
                        JField field = storeField.getFieldRef().resolve();
                        Pointer ptrXf = pointerFlowGraph.getInstanceField(obj, field);
                        addPFGEdge(ptrY, ptrXf);
                    }
                    // y = x.f (instance)
                    for (LoadField loadField : var.getLoadFields()) {
                        Var y = loadField.getLValue();
                        Pointer ptrY = pointerFlowGraph.getVarPtr(y);
                        JField field = loadField.getFieldRef().resolve();
                        Pointer ptrXf = pointerFlowGraph.getInstanceField(obj, field);
                        addPFGEdge(ptrXf, ptrY);
                    }
                    // x[i] = y
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        Var y = storeArray.getRValue();
                        Pointer ptrY = pointerFlowGraph.getVarPtr(y);
                        Pointer ptrArrayX = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(ptrY, ptrArrayX);
                    }
                    // y = x[i]
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        Var y = loadArray.getLValue();
                        Pointer ptrY = pointerFlowGraph.getVarPtr(y);
                        Pointer ptrArrayX = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(ptrArrayX, ptrY);
                    }
                    // r = x.k()
                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet ptn = pointer.getPointsToSet();
        PointsToSet diff = new PointsToSet();
        for (Obj obj : pointsToSet) {
            if (!ptn.contains(obj)) {
                diff.addObject(obj);
                // pt(n) ⋃= pts
                ptn.addObject(obj);
            }
        }
        if (diff.isEmpty()) { return diff; }
        for (Pointer succPointer : pointerFlowGraph.getSuccsOf(pointer)) {
            workList.addEntry(succPointer, diff);
        }
        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke invoke : var.getInvokes()) {
            if (invoke.isStatic()) { continue; }
            JMethod method = resolveCallee(recv, invoke);
            if (method == null) { continue; }
            IR methodIR = method.getIR();
            Var thisVar = methodIR.getThis();
            Pointer thisPointer = pointerFlowGraph.getVarPtr(thisVar);
            workList.addEntry(thisPointer, new PointsToSet(recv));
            CallKind callKind = null;
            if (invoke.isDynamic()) { callKind = CallKind.DYNAMIC; }
            if (invoke.isSpecial()) { callKind = CallKind.SPECIAL; }
            if (invoke.isVirtual()) { callKind = CallKind.VIRTUAL; }
            if (invoke.isInterface()) { callKind = CallKind.INTERFACE; }
            if (callGraph.addEdge(new Edge<>(callKind, invoke, method))) {
                addReachable(method);
                InvokeExp invokeExp = invoke.getInvokeExp();
                int count = invokeExp.getArgCount();
                for  (int i = 0; i < count; i++) {
                    Var ai = invokeExp.getArg(i);
                    Var pi = methodIR.getParam(i);
                    Pointer aiPtr = pointerFlowGraph.getVarPtr(ai);
                    Pointer piPtr = pointerFlowGraph.getVarPtr(pi);
                    addPFGEdge(aiPtr, piPtr);
                }
                Var R = invoke.getLValue();
                if (R != null) {
                    Pointer ptrR = pointerFlowGraph.getVarPtr(invoke.getLValue());
                    List<Var> retVars = methodIR.getReturnVars();
                    for (Var retVar : retVars) {
                        Pointer ptrRV = pointerFlowGraph.getVarPtr(retVar);
                        addPFGEdge(ptrRV, ptrR);
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
