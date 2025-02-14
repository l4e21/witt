
:- dynamic elem/2.
:- dynamic equal/2.

elem(x, 4).
elem(y, 6).
equal((elem(S1, A) -> true; elem(S2, A) -> true), elem(union(S1, S2), A)).

infer(P, Q) :- P -> assertz(Q).

by_contradiction(Clause, Commands) :-
    assertz(not(Clause)),
    Commands,
    not(Clause) -> Clause,
    retract(not(Clause)).
                   
prove(elem(union(x, y), 4)) :-
    Clause = elem(union(x, y), 4),
    by_contradiction(Clause, (LHS = (elem(_, A) -> true; elem(_, A) -> true),
                              equal(LHS, RHS),
                              term_variables(equal(LHS, RHS), [x, 4, y]),
                              infer(LHS, RHS),
                              Clause = RHS)). 

% ?- prove(elem(union(x, y), 4)).
%@ true.

% ?- not(elem(union(x, y), 4)).
%@ false.

% ?- elem(union(x, y), 4).
%@ true.

