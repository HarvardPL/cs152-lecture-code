datatype exp =
| EInt(v: int)
| EVar(x: string)
| EAdd(e1: exp, e2: exp)
| EMul(e1: exp, e2: exp)

function eval(e: exp, env: string -> int): int
{
    match e
    case EInt(v) => v
    case EVar(x) => env(x)
    case EAdd(e1, e2) => eval(e1, env) + eval(e2, env)
    case EMul(e1, e2) => eval(e1, env) * eval(e2, env)
}

function optimize(e: exp): exp
{
    match e
    case EInt(v) => e
    case EVar(x) => e
    case EAdd(e1, e2) => (match (optimize(e1), optimize(e2))
        case (EInt(v1), EInt(v2)) => EInt(v1+v2)
        case (EInt(0), e2) => e2
        case (e1, EInt(0)) => e1
        case (e1, e2) => EAdd(e1, e2))
    case EMul(e1, e2) => (match (optimize(e1), optimize(e2))
        case (EInt(v1), EInt(v2)) => EInt(v1*v2)
        case (EInt(0), e2) => EInt(0)
        case (e1, EInt(0)) => EInt(0)
        case (EInt(1), e2) => e2
        case (e1, EInt(1)) => e1
        case (e1, e2) => EMul(e1, e2))
}

lemma OptimizerPreservesSemantics(e: exp, env: string -> int)
ensures eval(optimize(e), env) == eval(e, env)
{
}

function {:spec} optimal(e: exp): bool
{
    match e
    case EInt(_) => true
    case EVar(_) => true
    case EAdd(EInt(_), EInt(_)) => false
    case EAdd(EInt(0), _) => false
    case EAdd(_, EInt(0)) => false
    case EAdd(e1, e2) => optimal(e1) && optimal(e2)
    case EMul(EInt(_), EInt(_)) => false
    case EMul(EInt(0), _) => false
    case EMul(_, EInt(0)) => false
    case EMul(EInt(1), _) => false
    case EMul(_, EInt(1)) => false
    case EMul(e1, e2) => optimal(e1) && optimal(e2)
}

lemma OptimizerIsOptimal(e: exp)
ensures optimal(optimize(e))
{
    // Structural induction on e
    match e {
        case EInt(v) => {
        }
        case EVar(x) => {
        }
        case EAdd(e1, e2) => {
            OptimizerIsOptimal(e1);
            OptimizerIsOptimal(e2);
        }
        case EMul(e1, e2) => {
            OptimizerIsOptimal(e1);
            OptimizerIsOptimal(e2);
        }
    }
}