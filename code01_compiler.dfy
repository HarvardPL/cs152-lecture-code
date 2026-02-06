// Compiler correctness proof for a stack machine
//
// The continuation-passing proof style originates from:
//   Xavier Leroy. "Formal verification of a realistic compiler."
//   Communications of the ACM, 52(7):107-115, 2009.
//   https://xavierleroy.org/publi/compcert-CACM.pdf
//
// See also: https://xavierleroy.org/courses/EUTypes-2019/

include "code01.dfy"

// Stack machine instructions
datatype instr = IPush(v: int) | ILoad(x: string) | IAdd | IMul

// Compile expression to stack machine code
function compile(e: exp): seq<instr>
{
    match e
    case EVar(x) => [ILoad(x)]
    case EInt(v) => [IPush(v)]
    case EAdd(e1, e2) => compile(e1) + compile(e2) + [IAdd]
    case EMul(e1, e2) => compile(e1) + compile(e2) + [IMul]
}

// Execute stack machine code
function exec(code: seq<instr>, stk: seq<int>, env: string -> int): seq<int>
    decreases code
{
    if code == [] then stk
    else match code[0]
        case IPush(v) => exec(code[1..], [v] + stk, env)
        case ILoad(x) => exec(code[1..], [env(x)] + stk, env)
        case IAdd => if |stk| >= 2 then exec(code[1..], [stk[1] + stk[0]] + stk[2..], env) else stk
        case IMul => if |stk| >= 2 then exec(code[1..], [stk[1] * stk[0]] + stk[2..], env) else stk
}

// Key insight: parameterize by continuation c to avoid separate composition lemma
lemma CompileCorrect(e: exp, c: seq<instr>, stk: seq<int>, env: string -> int)
    ensures exec(compile(e) + c, stk, env) == exec(c, [eval(e, env)] + stk, env)
{
    match e
    case EVar(x) =>
    case EInt(v) =>
    case EAdd(e1, e2) =>
        var v1 := eval(e1, env);
        assert compile(e) + c == compile(e1) + (compile(e2) + [IAdd] + c);
        assert compile(e2) + [IAdd] + c == compile(e2) + ([IAdd] + c);
        assert [eval(e2, env)] + ([v1] + stk) == [eval(e2, env), v1] + stk;
    case EMul(e1, e2) =>
        var v1 := eval(e1, env);
        assert compile(e) + c == compile(e1) + (compile(e2) + [IMul] + c);
        assert compile(e2) + [IMul] + c == compile(e2) + ([IMul] + c);
        assert [eval(e2, env)] + ([v1] + stk) == [eval(e2, env), v1] + stk;
}

// Main theorem: compiled code evaluates correctly
lemma CompilerCorrect(e: exp, env: string -> int)
    ensures exec(compile(e), [], env) == [eval(e, env)]
{
    CompileCorrect(e, [], [], env);
    assert compile(e) + [] == compile(e);
}

// Without automatic induction, explicit recursive calls are required
lemma {:induction false} CompileCorrectManual(e: exp, c: seq<instr>, stk: seq<int>, env: string -> int)
    ensures exec(compile(e) + c, stk, env) == exec(c, [eval(e, env)] + stk, env)
{
    match e
    case EVar(x) =>
    case EInt(v) =>
    case EAdd(e1, e2) =>
        var v1 := eval(e1, env);
        assert compile(e) + c == compile(e1) + (compile(e2) + [IAdd] + c);
        CompileCorrectManual(e1, compile(e2) + [IAdd] + c, stk, env);
        assert compile(e2) + [IAdd] + c == compile(e2) + ([IAdd] + c);
        CompileCorrectManual(e2, [IAdd] + c, [v1] + stk, env);
        assert [eval(e2, env)] + ([v1] + stk) == [eval(e2, env), v1] + stk;
    case EMul(e1, e2) =>
        var v1 := eval(e1, env);
        assert compile(e) + c == compile(e1) + (compile(e2) + [IMul] + c);
        CompileCorrectManual(e1, compile(e2) + [IMul] + c, stk, env);
        assert compile(e2) + [IMul] + c == compile(e2) + ([IMul] + c);
        CompileCorrectManual(e2, [IMul] + c, [v1] + stk, env);
        assert [eval(e2, env)] + ([v1] + stk) == [eval(e2, env), v1] + stk;
}

// Concrete example: 2 + (3 * 4) = 14
lemma {:timeLimit 30} Example()
{
    var e := EAdd(EInt(2), EMul(EInt(3), EInt(4)));
    var env: string -> int := _ => 0;
    assert compile(e) == [IPush(2), IPush(3), IPush(4), IMul, IAdd];
    CompilerCorrect(e, env);
    assert exec(compile(e), [], env) == [14];
}
