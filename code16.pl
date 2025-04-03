in((X,A),G) :- member((X,A),G), !.

/* version with the occurs check, faithful to simply-typed lambda calculus */
ty(G,var(X),A) :- in((X,A),G).
ty(G,lam(X,M),to(A,B)) :- ty([(X,A)|G],M,B).
ty(G,app(M,N),Res) :- ty(G,M,Fun), ty(G,N,Arg),
  unify_with_occurs_check(Fun,to(Arg,Res)).

/* version without the occurs check, causing infinite types */
ty_inf(G,var(X),A) :- in((X,A),G).
ty_inf(G,lam(X,M),to(A,B)) :- ty_inf([(X,A)|G],M,B).
ty_inf(G,app(M,N),Res) :- ty_inf(G,M,to(Arg,Res)), ty_inf(G,N,Arg).

/*
?- ty([],lam(x,var(x)),T).
T = to(_A, _A) ;
false.

?- ty([],lam(x,app(var(x),var(x))),T).
false.

?- ty([],T,to(x,x)).
T = lam(_A, var(_A)) .

?- ty([],lam(x,lam(y,var(x))),T).
T = to(_A, to(_, _A)) ;
false.
*/

/*
?- ty_inf([],lam(x,var(x)),T).
T = to(_A, _A) ;
false.

?- ty_inf([],lam(x,app(var(x),var(x))),T).
T = to(_S1, _A), % where
    _S1 = to(_S1, _A) .

?- ty_inf([],T,to(x,x)).
T = lam(_A, var(_A)) .

?- ty_inf([],lam(x,lam(y,var(x))),T).
T = to(_A, to(_, _A)) ;
false.
*/
