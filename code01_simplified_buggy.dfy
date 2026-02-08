datatype exp =
| EVar(x: string)
| EInt(v: int)
| EAdd(e1: exp, e2: exp)

function optimize(e: exp): exp
{
    match e
    case EVar(x) => e
    case EInt(v) => e
    case EAdd(EInt(0), e2) => optimize(e2)
    case EAdd(e1, EInt(0)) => optimize(e1)
    case EAdd(e1, e2) => EAdd(optimize(e1), optimize(e2))
}

function {:spec} optimal(e: exp): bool
{
    match e
    case EVar(_) => true
    case EInt(_) => true
    case EAdd(EInt(0), _) => false
    case EAdd(_, EInt(0)) => false
    case EAdd(e1, e2) => optimal(e1) && optimal(e2)
}

// BUG: can't be proved!
lemma {:axiom} OptimizerIsOptimal(e: exp)
ensures optimal(optimize(e))
