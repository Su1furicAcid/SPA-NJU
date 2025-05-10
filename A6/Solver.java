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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (callGraph.addReachableMethod(csMethod)) {
            StmtProcessor processor = new StmtProcessor(csMethod);
            for (Stmt stmt : csMethod.getMethod().getIR()) {
                stmt.accept(processor);
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            // x = new T()
            Var varX = stmt.getLValue();
            CSVar cxtVarX = csManager.getCSVar(context, varX);
            Obj as = heapModel.getObj(stmt);
            CSObj cxtAs = csManager.getCSObj(contextSelector.selectHeapContext(csMethod, as), as);
            PointsToSet cxtPts = PointsToSetFactory.make(cxtAs);
            workList.addEntry(cxtVarX, cxtPts);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            // x = y
            Var varX = stmt.getLValue();
            Var varY = stmt.getRValue();
            CSVar cxtVarX = csManager.getCSVar(context, varX);
            CSVar cxtVarY = csManager.getCSVar(context, varY);
            addPFGEdge(cxtVarY, cxtVarX);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            // y = x.f (static)
            if (stmt.isStatic()) {
                Var varY = stmt.getLValue();
                CSVar cxtVarY = csManager.getCSVar(context, varY);
                JField field = stmt.getFieldRef().resolve();
                StaticField fieldXf = csManager.getStaticField(field);
                addPFGEdge(fieldXf, cxtVarY);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            // x.f = y (static)
            if (stmt.isStatic()) {
                Var varY = stmt.getRValue();
                CSVar cxtVarY = csManager.getCSVar(context, varY);
                JField field = stmt.getFieldRef().resolve();
                StaticField fieldXf = csManager.getStaticField(field);
                addPFGEdge(cxtVarY, fieldXf);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            // y = x.m(a1, ..., an) (static)
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context targetCxt = contextSelector.selectContext(csCallSite, callee);
                CSMethod csMethod = csManager.getCSMethod(targetCxt, callee);
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, csMethod))) {
                    addReachable(csMethod);
                    InvokeExp invokeExp = stmt.getInvokeExp();
                    IR methodIR = callee.getIR();
                    int count = invokeExp.getArgCount();
                    for (int i = 0; i < count; i++) {
                        Var ai = invokeExp.getArg(i);
                        Var pi = methodIR.getParam(i);
                        CSVar cxtAi = csManager.getCSVar(context, ai);
                        CSVar cxtPi = csManager.getCSVar(targetCxt, pi);
                        addPFGEdge(cxtAi, cxtPi);
                    }
                    Var varY = stmt.getLValue();
                    if (varY != null) {
                        CSVar cxtVarY = csManager.getCSVar(context, varY);
                        for (Var retVar : methodIR.getReturnVars()) {
                            CSVar cxtRetVar = csManager.getCSVar(targetCxt, retVar);
                            addPFGEdge(cxtRetVar, cxtVarY);
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
            if (entry == null) { continue; }
            Pointer ptrX = entry.pointer();
            PointsToSet ptsX = entry.pointsToSet();
            PointsToSet diff = propagate(ptrX, ptsX);
            if (diff.isEmpty()) { continue; }
            if (ptrX instanceof CSVar cxtVarX) {
                for (CSObj csObj : diff) {
                    Context xContext = cxtVarX.getContext();
                    // x.f = y (instance)
                    for (StoreField storeField : cxtVarX.getVar().getStoreFields()) {
                        if (storeField.isStatic()) { continue; }
                        Var varY = storeField.getRValue();
                        CSVar cxtVarY = csManager.getCSVar(xContext, varY);
                        JField field = storeField.getFieldRef().resolve();
                        InstanceField cxtField = csManager.getInstanceField(csObj, field);
                        addPFGEdge(cxtVarY, cxtField);
                    }
                    // y = x.f (instance)
                    for (LoadField loadField : cxtVarX.getVar().getLoadFields()) {
                        if (loadField.isStatic()) { continue; }
                        Var varY = loadField.getLValue();
                        CSVar cxtVarY = csManager.getCSVar(xContext, varY);
                        JField field = loadField.getFieldRef().resolve();
                        InstanceField cxtField = csManager.getInstanceField(csObj, field);
                        addPFGEdge(cxtField, cxtVarY);
                    }
                    // x[i] = y (instance)
                    for (StoreArray storeArray : cxtVarX.getVar().getStoreArrays()) {
                        Var varY = storeArray.getRValue();
                        CSVar cxtVarY = csManager.getCSVar(xContext, varY);
                        ArrayIndex cxtArrXi = csManager.getArrayIndex(csObj);
                        addPFGEdge(cxtVarY, cxtArrXi);
                    }
                    // y = x[i] (instance)
                    for (LoadArray loadArray : cxtVarX.getVar().getLoadArrays()) {
                        Var  varY = loadArray.getLValue();
                        CSVar cxtVarY = csManager.getCSVar(xContext, varY);
                        ArrayIndex cxtArrXi = csManager.getArrayIndex(csObj);
                        addPFGEdge(cxtArrXi, cxtVarY);
                    }
                    // x.m(...)
                    processCall(cxtVarX, csObj);
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
        PointsToSet diff = PointsToSetFactory.make();
        for (CSObj obj : pointsToSet) {
            if (!ptn.contains(obj)) {
                diff.addObject(obj);
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        for (Invoke invoke : recv.getVar().getInvokes()) {
            if (invoke.isStatic()) { continue; }
            JMethod callee = resolveCallee(recvObj, invoke);
            if (callee == null) { continue; }
            // c
            Context recvContext = recv.getContext();
            // c:x
            CSCallSite csCallSite = csManager.getCSCallSite(recvContext, invoke);
            // c^{t}
            Context targetCxt = contextSelector.selectContext(csCallSite, recvObj, callee);
            // c^{t}:m
            CSMethod csMethod = csManager.getCSMethod(targetCxt, callee);
            IR methodIR = callee.getIR();
            Var thisVar = methodIR.getThis();
            // c^{t}:m_{this}
            CSVar cxtVarThis = csManager.getCSVar(targetCxt, thisVar);
            workList.addEntry(cxtVarThis, PointsToSetFactory.make(recvObj));
            CallKind callKind = null;
            if (invoke.isDynamic()) { callKind = CallKind.DYNAMIC; }
            if (invoke.isSpecial()) { callKind = CallKind.SPECIAL; }
            if (invoke.isVirtual()) { callKind = CallKind.VIRTUAL; }
            if (invoke.isInterface()) { callKind = CallKind.INTERFACE; }
            if (callGraph.addEdge(new Edge<>(callKind, csCallSite, csMethod))) {
                addReachable(csMethod);
                InvokeExp invokeExp = invoke.getInvokeExp();
                int count = invokeExp.getArgCount();
                for (int i = 0; i < count; i++) {
                    Var ai = invokeExp.getArg(i);
                    Var pi = methodIR.getParam(i);
                    CSVar cxtVarAi = csManager.getCSVar(recvContext, ai);
                    CSVar cxtVarPi = csManager.getCSVar(targetCxt, pi);
                    addPFGEdge(cxtVarAi, cxtVarPi);
                }
                Var varY = invoke.getLValue();
                if (varY != null) {
                    CSVar cxtVarY = csManager.getCSVar(recvContext, varY);
                    for (Var retVar : methodIR.getReturnVars()) {
                        CSVar cxtVarRet = csManager.getCSVar(targetCxt, retVar);
                        addPFGEdge(cxtVarRet, cxtVarY);
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
