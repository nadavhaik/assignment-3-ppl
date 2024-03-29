// L4-eval-box.ts
// L4 with mutation (set!) and env-box model
// Direct evaluation of letrec with mutation, define supports mutual recursion.

import { map, repeat, zipWith } from "ramda";
import {
    isBoolExp,
    isCExp,
    isLitExp,
    isNumExp,
    isPrimOp,
    isStrExp,
    isVarRef,
    isSetExp,
    isAppExp,
    isDefineExp,
    isIfExp,
    isLetrecExp,
    isLetExp,
    isProcExp,
    Binding,
    VarDecl,
    VarRef,
    CExp,
    Exp,
    IfExp,
    LetrecExp,
    LetExp,
    ProcExp,
    Program,
    SetExp,
    parseL4Exp,
    DefineExp,
    isTraceExp as isTraceExp,
    TraceExp,
    makeVarRef,
    makeTracedExp, AppExp
} from "./L4-ast";
import { applyEnv, applyEnvBdg, globalEnvAddBinding, makeExtEnv, setFBinding,
            theGlobalEnv, Env, FBinding} from "./L4-env-box";
import { isClosure, makeClosure, Closure, Value, valueToString, TracedClosure, isTracedClosure, makeTracedClosure } from "./L4-value-box";
import { applyPrimitive } from "./evalPrimitive-box";
import { first, rest, isEmpty, cons } from "../shared/list";
import {Result, bind, mapv, mapResult, makeFailure, makeOk, isFailure, isOk} from "../shared/result";
import { parse as p } from "../shared/parser";
import {unbox} from "../shared/box";
import {isString} from "../shared/type-predicates";

// ========================================================
// Eval functions

const applicativeEval = (exp: CExp, env: Env,tracedRators: any): Result<Value> => {
    // console.log(`applicativeEval => exp: ${JSON.stringify(exp)}`)
    if(isNumExp(exp)) return makeOk(exp.val)
    if(isBoolExp(exp)) return makeOk(exp.val)
    if(isStrExp(exp)) return makeOk(exp.val)
    if(isPrimOp(exp)) return makeOk(exp)
    if(isVarRef(exp)) return evalVarRef(exp, env,tracedRators)
    if(isLitExp(exp)) return makeOk(exp.val as Value)
    if(isIfExp(exp)) return evalIf(exp, env,tracedRators)
    if(isProcExp(exp)) return evalProc(exp, env)
    if(isLetExp(exp)) return evalLet(exp, env,tracedRators)
    if(isLetrecExp(exp)) return evalLetrec(exp, env,tracedRators)
    if(isSetExp(exp)) return evalSet(exp, env,tracedRators)
    if(isAppExp(exp)) return bind(applicativeEval(exp.rator, env, tracedRators), (proc: Value) =>
                bind(mapResult((rand: CExp) => applicativeEval(rand, env, tracedRators), exp.rands), (args: Value[]) =>
                    applyProcedure(proc, args, tracedRators)))
    if(isTraceExp(exp)) return evalTraceExp(exp,tracedRators) // HW3
    return exp;

}

export const evalVarRef = (v: VarRef, env: Env, tracedRators: any): Result<Value> => {
    let valRes = applyEnv(env, v.var)
    if(isFailure(valRes) || !isTraced(v.var,tracedRators))
        return valRes

    let val = valRes.value
    if(!isClosure(val))
        return makeFailure(`Cannot trace a non closure expression: ${v.var}`)

    return makeOk(makeTracedClosure(v.var, val.params, val.body, env))
}
export const isTrueValue = (x: Value): boolean =>
    ! (x === false);

const trace = (v: VarRef, tracedRators: any): void => { tracedRators[v.var] = 0 }
const isTraced = (rator: string,tracedRators: any): boolean => tracedRators.hasOwnProperty(rator)

// HW3
const evalTraceExp = (exp: TraceExp,tracedRators: any): Result<void> => makeOk(trace(exp.var,tracedRators))


// HW3 use these functions
const printPreTrace = (name: string, vals: Value[], counter: number): void =>
    console.log(`>${" >".repeat(counter)} (${name} ${map(valueToString, vals)})`)

const printPostTrace = (val: Value, counter: number): void =>
    console.log(`<${" <".repeat(counter)} ${val}`)


const evalIf = (exp: IfExp, env: Env, tracedRators: any): Result<Value> =>
    bind(applicativeEval(exp.test, env,tracedRators), (test: Value) =>
        isTrueValue(test) ? applicativeEval(exp.then, env,tracedRators) :
        applicativeEval(exp.alt, env,tracedRators));

const evalProc = (exp: ProcExp, env: Env): Result<Closure> =>
    makeOk(makeClosure(exp.args, exp.body, env));

// KEY: This procedure does NOT have an env parameter.
//      Instead we use the env of the closure.
const applyProcedure = (proc: Value, args: Value[],tracedRators: any): Result<Value> =>
    isPrimOp(proc) ? applyPrimitive(proc, args) :
    isClosure(proc) ? applyClosure(proc, args, tracedRators) :
    isTracedClosure(proc) ? applyTracedClosure(proc, args,tracedRators) :
    makeFailure(`Bad procedure ${JSON.stringify(proc)}`);

const applyClosure = (proc: Closure, args: Value[], tracedRators: any): Result<Value> => {
    const vars = map((v: VarDecl) => v.var, proc.params);
    return evalSequence(proc.body, makeExtEnv(vars, args, proc.env), tracedRators);
}

const applyTracedClosure = (proc: TracedClosure, args: Value[],tracedRators: any): Result<Value> => {
    printPreTrace(proc.name, args, tracedRators[proc.name])
    tracedRators[proc.name]++
    let res = applyClosure(proc.closure, args, tracedRators)
    tracedRators[proc.name]--
    if(isOk(res))
        printPostTrace(res.value, tracedRators[proc.name])


    return res
}



// Evaluate a sequence of expressions (in a program)
export const evalSequence = (seq: Exp[], env: Env,tracedRators:any): Result<Value> => {
    // console.log(`evalSequence => exp: ${JSON.stringify(seq)}`)
    return isEmpty(seq) ? makeFailure("Empty program") : evalCExps(first(seq), rest(seq), env,tracedRators);
}
    
const evalCExps = (first: Exp, rest: Exp[], env: Env,tracedRators:any): Result<Value> =>
    isDefineExp(first) ? evalDefineExps(first, rest,tracedRators) :
    isCExp(first) && isEmpty(rest) ? applicativeEval(first, env,tracedRators) :
    isCExp(first) ? bind(applicativeEval(first, env,tracedRators), _ => evalSequence(rest, env,tracedRators)) :
    first;

// Eval a sequence of expressions when the first exp is a Define.
// Compute the rhs of the define, extend the env with the new binding
// then compute the rest of the exps in the new env.
// L4-BOX @@
// define always updates theGlobalEnv
// We also only expect defineExps at the top level.
const evalDefineExps = (def: DefineExp, exps: Exp[],tracedRators:any): Result<Value> =>
    bind(applicativeEval(def.val, theGlobalEnv,tracedRators), (rhs: Value) => {
            globalEnvAddBinding(def.var.var, rhs);
            return evalSequence(exps, theGlobalEnv,tracedRators);
        });

// Main program
// L4-BOX @@ Use GE instead of empty-env
export const evalProgram = (program: Program): Result<Value> => {
    return evalSequence(program.exps, theGlobalEnv,{});
}

export const evalParse = (s: string): Result<Value> =>
    bind(p(s), (x) =>
            bind(parseL4Exp(x), (exp: Exp) =>
                evalSequence([exp], theGlobalEnv,{})));

// LET: Direct evaluation rule without syntax expansion
// compute the values, extend the env, eval the body.
const evalLet = (exp: LetExp, env: Env,tracedRators: any): Result<Value> => {
    const vals = mapResult((v: CExp) => applicativeEval(v, env,tracedRators), map((b: Binding) => b.val, exp.bindings));
    const vars = map((b: Binding) => b.var.var, exp.bindings);
    return bind(vals, (vals: Value[]) => evalSequence(exp.body, makeExtEnv(vars, vals, env),tracedRators));
}

// @@ L4-EVAL-BOX 
// LETREC: Direct evaluation rule without syntax expansion
// 1. extend the env with vars initialized to void (temporary value)
// 2. compute the vals in the new extended env
// 3. update the bindings of the vars to the computed vals
// 4. compute body in extended env
const evalLetrec = (exp: LetrecExp, env: Env,tracedRators: any): Result<Value> => {
    const vars = map((b: Binding) => b.var.var, exp.bindings);
    const vals = map((b: Binding) => b.val, exp.bindings);
    const extEnv = makeExtEnv(vars, repeat(undefined, vars.length), env);
    // @@ Compute the vals in the extended env
    const cvalsResult = mapResult((v: CExp) => applicativeEval(v, extEnv,tracedRators), vals);
    const result = mapv(cvalsResult, (cvals: Value[]) => 
                        zipWith((bdg, cval) => setFBinding(bdg, cval), extEnv.frame.fbindings, cvals));
    return bind(result, _ => evalSequence(exp.body, extEnv,tracedRators));
};

// L4-eval-box: Handling of mutation with set!
const evalSet = (exp: SetExp, env: Env,tracedRators:any): Result<void> =>
    bind(applicativeEval(exp.val, env,tracedRators), (val: Value) =>
        mapv(applyEnvBdg(env, exp.var.var), (bdg: FBinding) =>
            setFBinding(bdg, val)));

