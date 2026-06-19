% must be run from the tmp directory!
:- consult('big_.prolog').
:-use_module(library(lists)).
:-use_module(library(thread)).

line_axiom(L,A) :- line(L,axiom(A)). % consult adds this

line_line_axioms_unify_find_cycles(L,R,B,Out) :- 
    line_axiom(L,A1),
    line_axiom(R,A2),
    (   A1 = A2 , cyclic_term(A1)
    ->  B = true,  Out = some(A1)
    ;   B = false, Out = none
    ).



write_result(L) :-
    line_axiom(L,_),
    % (exists_directory('prolog') -> true ; make_directory('prolog')),
    (exists_directory('prolog_cycles/results') -> true ; make_directory_path('prolog_cycles/results')),
    atom_chars('prolog_cycles/results/axiom_',Results),
    atom_chars(L,LineNumber),
    atom_chars('.metta',Extension),
    append(Results,LineNumber,RL),
    append(RL,Extension,FileNameStr),
    atom_chars(FileName,FileNameStr),

    open(FileName, write, Stream),
    forall( line_line_axioms_unify_find_cycles(L,R,B,_)
    ,       (B = true -> format(Stream, '(cycles ~w ~w)~n', [L,R]); true)
    ),

    write(FileName),
    nl,
    close(Stream).  

write_all_results_concurrent :- 
    pwd,
    
    findall(L, line_axiom(L,_), Bag),
    concurrent_maplist(write_result, Bag).
    
