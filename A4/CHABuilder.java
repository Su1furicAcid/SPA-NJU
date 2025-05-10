package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod jmethod = workList.poll();
            if (callGraph.reachableMethods.contains(jmethod)) {
                continue;
            }
            callGraph.addReachableMethod(jmethod);
            Set<Invoke> callSites = callGraph.getCallSitesIn(jmethod);
            for (Invoke cs : callSites) {
                Set<JMethod> T = resolve(cs);
                if (T == null) {
                    continue;
                }
                for (JMethod jm : T) {
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs), cs, jm));
                    workList.add(jm);
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        MethodRef methodRef = callSite.getMethodRef();
        JClass cls = methodRef.getDeclaringClass();
        Subsignature subsignature = methodRef.getSubsignature();
        Set<JMethod> T = new HashSet<>();
        CallKind kind = CallGraphs.getCallKind(callSite);
        switch (kind) {
            case STATIC, SPECIAL:
                T.add(dispatch(cls, subsignature));
                break;
            case VIRTUAL, INTERFACE:
                Set<JClass> seen = new HashSet<>();
                Queue<JClass> classQueue = new LinkedList<>();
                classQueue.add(cls);
                seen.add(cls);
                while (!classQueue.isEmpty()) {
                    JClass current = classQueue.poll();
                    JMethod target = dispatch(current, subsignature);
                    if (target != null && !target.isAbstract()) {
                        T.add(target);
                    }
                    for (JClass sub : hierarchy.getDirectSubclassesOf(current)) {
                        if (seen.add(sub)) {
                            classQueue.add(sub);
                        }
                    }
                    for (JClass impl : hierarchy.getDirectImplementorsOf(current)) {
                        if (seen.add(impl)) {
                            classQueue.add(impl);
                        }
                    }
                    for (JClass subInterface : hierarchy.getDirectSubinterfacesOf(current)) {
                        if (seen.add(subInterface)) {
                            classQueue.add(subInterface);
                        }
                    }
                }
                break;
        }
        return T;
    }

    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod sig = jclass.getDeclaredMethod(subsignature);
        if (sig != null) {
            return sig;
        } else {
            JClass sup = jclass.getSuperClass();
            if (sup != null && !jclass.isInterface()) {
                return dispatch(sup, subsignature);
            } else {
                return null;
            }
        }
    }
}