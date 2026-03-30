// Verus PCell example: linear ghost permissions
// Source: https://github.com/verus-lang/verus/blob/main/examples/cells.rs
// See also: Lattuada et al., "Verus: Verifying Rust Programs
//   using Linear Ghost Types," OOPSLA 2023.
//   https://dl.acm.org/doi/10.1145/3586037

#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::{cell::*, *};

verus! {

struct X {
    pub i: u64,
}

fn main() {
    let x = X { i: 5 };

    // PCell::empty() returns the cell AND a tracked ghost token.
    // The token is a linear ghost value: it exists only during
    // verification, and is erased at compile time.
    let (pcell, Tracked(mut token)) = PCell::empty();

    // To write to the cell, we must pass the token.
    // put() takes &mut token: exclusive access to the permission.
    pcell.put(Tracked(&mut token), x);

    // The verifier can now assert what the cell contains,
    // because the token tracks the cell's state.
    assert(token.mem_contents() === MemContents::Init(X { i: 5 }));
}

} // verus!
