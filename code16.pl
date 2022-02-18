in((X,A),G) :- member((X,A),G), !.

ty(G,v(X),A) :- in((X,A),G).
ty(G,l(X,M),to(A,B)) :- ty([(X,A)|G],M,B).
ty(G,a(M,N),Res) :- ty(G,M,Fun), ty(G,N,Arg),
  unify_with_occurs_check(Fun,to(Arg,Res)).

/*
?- ty([],l(x,v(x)),T).
T = to(_1140, _1140) ;
false.

?- ty([],l(x,a(v(x),v(x))),T).
false.

?- ty([],T,to(x,x)).
T = l(_4410, v(_4410)) .

?- ty([],l(x,l(y,v(x))),T).
T = to(_5908, to(_5926, _5908)) .
*/
