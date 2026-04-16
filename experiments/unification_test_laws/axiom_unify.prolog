% must be run from the tmp directory!
:- consult('big_.prolog').
:-use_module(library(lists)).
:-use_module(library(thread)).

line_axiom(L,A) :- line(L,axiom(A)). % consult adds this

line_line_axioms_unify(L,R,B,Out) :- 
    line_axiom(L,A1),
    line_axiom(R,A2),
    (   unify_with_occurs_check(A1, A2)
    ->  B = true,  Out = some(A1)
    ;   B = false, Out = none
    ).



write_result(L) :-
    line_axiom(L,_),
    % (exists_directory('prolog') -> true ; make_directory('prolog')),
    (exists_directory('prolog/results') -> true ; make_directory_path('prolog/results')),
    atom_chars('prolog/results/axiom_',Results),
    atom_chars(L,LineNumber),
    atom_chars('.metta',Extension),
    append(Results,LineNumber,RL),
    append(RL,Extension,FileNameStr),
    atom_chars(FileName,FileNameStr),

    open(FileName, write, Stream),
    forall( line_line_axioms_unify(L,R,B,_)
    ,       (B = true -> format(Stream, '(unifies ~w ~w)~n', [L,R]); true)
    ),

    write(FileName),
    nl,
    close(Stream).  

write_all_results_concurrent :- 
    pwd,
    
    findall(L, line_axiom(L,_), Bag),
    concurrent_maplist(write_result, Bag).
    
