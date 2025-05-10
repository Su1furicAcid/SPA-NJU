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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.Assignment;
import pascal.taie.analysis.Analysis;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;
import java.util.Map;
import java.util.Optional;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        // Because we do not support inter-procedure analysis, so
        // we can only assume that parameter is NAC.
        CPFact boundaryFact = new CPFact();
        List<Var> params = cfg.getMethod().getIR().getParams();
        for (Var var : params) {
            if (canHoldInt(var)) {
                boundaryFact.update(var, Value.getNAC());
            }
        }
        return boundaryFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Map.Entry<Var, Value> entry: fact.entries().toList()) {
            Var var = entry.getKey();
            Value value = entry.getValue();
            Value targetValue = target.get(var);
            target.update(var, meetValue(value, targetValue));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        // NAC meet v
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        // v meet c
        if (v1.isConstant() && v2.isConstant()) {
            // v meet c || c meet c
            if (!v1.equals(v2)) {
                return Value.getNAC();
            } else {
                return Value.makeConstant(v1.getConstant());
            }
        }
        // UNDEF meet v
        if (v1.isConstant() && v2.isUndef()) {
            return Value.makeConstant(v1.getConstant());
        }
        if (v1.isUndef() && v2.isConstant()) {
            return Value.makeConstant(v2.getConstant());
        }
        if (v1.isUndef() && v2.isUndef()) {
            return Value.getUndef();
        }
        // Other
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        boolean change = false;
        CPFact newOut = in.copy();
        if (stmt instanceof DefinitionStmt<?,?> defStmt) {
            LValue lvalue = defStmt.getLValue();
            RValue rvalue = defStmt.getRValue();
            if (lvalue instanceof Var var) {
                if (canHoldInt(var)) {
                    Value evaluated = evaluate(rvalue, in);
                    newOut.update(var, evaluated);
                }
            }
        }
        change = out.copyFrom(newOut);
        return change;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof Var) {
            return in.get((Var) exp);
        }
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        if (exp instanceof BinaryExp) {
            if (exp instanceof ArithmeticExp arithmeticExp) {
                Value leftVal = evaluate(arithmeticExp.getOperand1(), in);
                Value rightVal = evaluate(arithmeticExp.getOperand2(), in);
                if (rightVal.isConstant() && rightVal.getConstant() == 0 &&
                        (arithmeticExp.getOperator() == ArithmeticExp.Op.DIV || arithmeticExp.getOperator() == ArithmeticExp.Op.REM)) {
                    return Value.getUndef();
                }
                if (leftVal.isConstant() && rightVal.isConstant()) {
                    int left = leftVal.getConstant();
                    int right = rightVal.getConstant();
                    return switch (arithmeticExp.getOperator()) {
                        case ADD -> Value.makeConstant(left + right);
                        case SUB -> Value.makeConstant(left - right);
                        case MUL -> Value.makeConstant(left * right);
                        case DIV -> Value.makeConstant(left / right);
                        case REM -> Value.makeConstant(left % right);
                        default -> Value.getUndef();
                    };
                }
                return leftVal.isNAC() || rightVal.isNAC() ? Value.getNAC() : Value.getUndef();
            }
            if (exp instanceof ConditionExp conditionExp) {
                Value leftVal = evaluate(conditionExp.getOperand1(), in);
                Value rightVal = evaluate(conditionExp.getOperand2(), in);
                if (leftVal.isConstant() && rightVal.isConstant()) {
                    int left = leftVal.getConstant();
                    int right = rightVal.getConstant();
                    return switch (conditionExp.getOperator()) {
                        case EQ -> Value.makeConstant(left == right ? 1 : 0);
                        case NE -> Value.makeConstant(left != right ? 1 : 0);
                        case LT -> Value.makeConstant(left < right ? 1 : 0);
                        case GT -> Value.makeConstant(left > right ? 1 : 0);
                        case LE -> Value.makeConstant(left <= right ? 1 : 0);
                        case GE -> Value.makeConstant(left >= right ? 1 : 0);
                        default -> Value.getUndef();
                    };
                }
                return leftVal.isNAC() || rightVal.isNAC() ? Value.getNAC() : Value.getUndef();
            }
            if (exp instanceof ShiftExp shiftExp) {
                Value leftVal = evaluate(shiftExp.getOperand1(), in);
                Value rightVal = evaluate(shiftExp.getOperand2(), in);
                if (leftVal.isConstant() && rightVal.isConstant()) {
                    int left = leftVal.getConstant();
                    int right = rightVal.getConstant();
                    return switch (shiftExp.getOperator()) {
                        case SHL -> Value.makeConstant(left << right);
                        case SHR -> Value.makeConstant(left >> right);
                        case USHR -> Value.makeConstant(left >>> right);
                        default -> Value.getUndef();
                    };
                }
                return leftVal.isNAC() || rightVal.isNAC() ? Value.getNAC() : Value.getUndef();
            }
            if (exp instanceof BitwiseExp bitwiseExp) {
                Value leftVal = evaluate(bitwiseExp.getOperand1(), in);
                Value rightVal = evaluate(bitwiseExp.getOperand2(), in);
                if (leftVal.isConstant() && rightVal.isConstant()) {
                    int left = leftVal.getConstant();
                    int right = rightVal.getConstant();
                    return switch (bitwiseExp.getOperator()) {
                        case AND -> Value.makeConstant(left & right);
                        case OR -> Value.makeConstant(left | right);
                        case XOR -> Value.makeConstant(left ^ right);
                        default -> Value.getUndef();
                    };
                }
                return leftVal.isNAC() || rightVal.isNAC() ? Value.getNAC() : Value.getUndef();
            }
        }
        return Value.getNAC();
    }
}
