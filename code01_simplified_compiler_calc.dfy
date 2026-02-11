include "code01_simplified_compiler.dfy"

// Calc version: shows the chain of equalities and where hints are needed
lemma CompileCorrectCalc(e: exp, c: seq<instr>, stk: seq<int>, env: string -> int)
    ensures exec(compile(e) + c, stk, env) == exec(c, [eval(e, env)] + stk, env)
{
    match e
    case EVar(x) =>
    case EInt(v) =>
    case EAdd(e1, e2) =>
        var v1 := eval(e1, env);
        var v2 := eval(e2, env);
        calc {
            exec(compile(e) + c, stk, env);
        ==  { assert compile(e) + c == compile(e1) + (compile(e2) + [IAdd] + c); }
            exec(compile(e1) + (compile(e2) + [IAdd] + c), stk, env);
        ==  exec(compile(e2) + [IAdd] + c, [v1] + stk, env);
        ==  { assert compile(e2) + [IAdd] + c == compile(e2) + ([IAdd] + c); }
            exec(compile(e2) + ([IAdd] + c), [v1] + stk, env);
        ==  exec([IAdd] + c, [v2] + ([v1] + stk), env);
        ==  { assert [v2] + ([v1] + stk) == [v2, v1] + stk; }
            exec([IAdd] + c, [v2, v1] + stk, env);
        ==  exec(c, [v1 + v2] + stk, env);
        ==  exec(c, [eval(e, env)] + stk, env);
        }
}

// Calc version with explicit recursive calls
lemma {:induction false} CompileCorrectCalcManual(e: exp, c: seq<instr>, stk: seq<int>, env: string -> int)
    ensures exec(compile(e) + c, stk, env) == exec(c, [eval(e, env)] + stk, env)
{
    match e
    case EVar(x) =>
    case EInt(v) =>
    case EAdd(e1, e2) =>
        var v1 := eval(e1, env);
        var v2 := eval(e2, env);
        calc {
            exec(compile(e) + c, stk, env);
        ==  { assert compile(e) + c == compile(e1) + (compile(e2) + [IAdd] + c); }
            exec(compile(e1) + (compile(e2) + [IAdd] + c), stk, env);
        ==  { CompileCorrectCalcManual(e1, compile(e2) + [IAdd] + c, stk, env); }
            exec(compile(e2) + [IAdd] + c, [v1] + stk, env);
        ==  { assert compile(e2) + [IAdd] + c == compile(e2) + ([IAdd] + c); }
            exec(compile(e2) + ([IAdd] + c), [v1] + stk, env);
        ==  { CompileCorrectCalcManual(e2, [IAdd] + c, [v1] + stk, env); }
            exec([IAdd] + c, [v2] + ([v1] + stk), env);
        ==  { assert [v2] + ([v1] + stk) == [v2, v1] + stk; }
            exec([IAdd] + c, [v2, v1] + stk, env);
        ==  exec(c, [v1 + v2] + stk, env);
        ==  exec(c, [eval(e, env)] + stk, env);
        }
}