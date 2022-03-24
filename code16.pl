in((X,A),G) :- member((X,A),G), !.

ty(G,var(X),A) :- in((X,A),G).
ty(G,lam(X,M),to(A,B)) :- ty([(X,A)|G],M,B).
ty(G,app(M,N),Res) :- ty(G,M,Fun), ty(G,N,Arg),
  unify_with_occurs_check(Fun,to(Arg,Res)).

/*
?- ty([],lam(x,var(x)),T).

?- ty([],lam(x,a(var(x),var(x))),T).

?- ty([],T,to(x,x)).

?- ty([],lam(x,lam(y,var(x))),T).
*/






/*
?- ty([],lam(x,var(x)),T).
T = to(_A, _A) ;
false.

?- ty([],lam(x,a(var(x),var(x))),T).
false.

?- ty([],T,to(x,x)).
T = lam(_A, var(_A)) .

?- ty([],lam(x,lam(y,var(x))),T).
T = to(_A, to(_, _A)) ;
false.
*/
