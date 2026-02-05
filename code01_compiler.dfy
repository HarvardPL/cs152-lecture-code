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
        assert compile(e) + c == compile(e1) + (compile(e2) + [IAdd] + c);  // seq assoc
        CompileCorrect(e1, compile(e2) + [IAdd] + c, stk, env);
        assert compile(e2) + [IAdd] + c == compile(e2) + ([IAdd] + c);      // seq assoc
        CompileCorrect(e2, [IAdd] + c, [v1] + stk, env);
        assert [eval(e2, env)] + ([v1] + stk) == [eval(e2, env), v1] + stk; // stack shape
    case EMul(e1, e2) =>
        var v1 := eval(e1, env);
        assert compile(e) + c == compile(e1) + (compile(e2) + [IMul] + c);
        CompileCorrect(e1, compile(e2) + [IMul] + c, stk, env);
        assert compile(e2) + [IMul] + c == compile(e2) + ([IMul] + c);
        CompileCorrect(e2, [IMul] + c, [v1] + stk, env);
        assert [eval(e2, env)] + ([v1] + stk) == [eval(e2, env), v1] + stk;
}

// Main theorem: compiled code evaluates correctly
lemma CompilerCorrect(e: exp, env: string -> int)
    ensures exec(compile(e), [], env) == [eval(e, env)]
{
    CompileCorrect(e, [], [], env);
    assert compile(e) + [] == compile(e);
}
