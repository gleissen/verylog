:- module(initial_pass, [run_initial_pass/0], [hidden(true)]).

:- use_module(library(lists)).

:- use_module('lib/misc.pl').
:- use_module('lib/ir.pl').

%% #############################################################################
%% ### INITIAL PASS OVER THE PROGRAM ###########################################
%% #############################################################################

:- dynamic b_written_to/1.

run_initial_pass :-
        retractall(b_written_to(_)),
        
        ir_toplevel_list(TopLevelPredicates),
        (   foreach(P, TopLevelPredicates)
        do  query_ir(P, PInsts),
            maplist(run_initial_toplevels(P), PInsts, _)
        ).

run_initial_toplevels(always, _Event-Stmt, _) :-
        !, Stmt =.. [Type|Args],
        run_initial_stmt(Type, Args, _).

run_initial_toplevels(module_inst, _Name-_Inputs-_Outputs, _) :- !.

run_initial_toplevels(link,_UFOut-_UFIns,_) :- !.
run_initial_toplevels(asn,L-R,_) :- !,
        (   \+ ir:wire(L) ->
            throwerr('assign ~p = ~p : lhs must be a wire', [L,R])
        ;   true
        ),
        (   is_uf(R) ->
            true
        ;   ir:register(R) ->
            true
        ;   ir:wire(R) ->
            true
        ;   otherwise ->
            throwerr('assign ~p = ~p : invalid rhs of continuous assignment', [L,R])
        ).

run_initial_toplevels(register,_,_) :- !.
run_initial_toplevels(wire,_,_) :- !.
run_initial_toplevels(taint_source,Source,_) :- !,
        (   \+ ir:register(Source) -> 
            throwerr('source register ~p does not exist', [Source])
        ; true
        ).
        
run_initial_toplevels(taint_sink,Sink,_) :- !,
        (   \+ ir:register(Sink) -> 
            throwerr('sink register ~p does not exist', [Sink])
        ; true
        ).

run_initial_toplevels(TL,P,_) :-
        throwerr('run_initial_toplevels is not yet implemented for ~p as in ~p~n', [TL,P]).

run_initial_stmt(ite,[Cond,Then,Else], _) :-
        !,
        ( \+ atom(Cond) -> throwerr('condition of ite(~p, ~p, ~p) is not an atom', [Cond,Then,Else])
        ; save(cond_atom(Cond))
        ),
        (   compound(Then) ->
            Then =.. [TypeThen|ArgThen],
            run_initial_stmt(TypeThen, ArgThen,_)
        ;   true
        ),
        (   compound(Else) ->
            Else =.. [TypeElse|ArgElse],
            run_initial_stmt(TypeElse, ArgElse,_)
        ;   true
        ).

run_initial_stmt(nb_asn,[_Lhs,_Rhs], _) :- !.

run_initial_stmt(b_asn,[L,R], _) :- !,
        (   b_written_to(R) ->
            throwerr('~p is read & written by blocking assignments !', [R])
        ;   true
        ),
        assert(b_written_to(L)).
        

run_initial_stmt(block,[Stmts], _) :- !,
        (   foreach(Stmt, Stmts)
        do  Stmt =.. [Type|Args],
            run_initial_stmt(Type,Args,_)
        ).

run_initial_stmt(skip,_,_) :- !.

run_initial_stmt(Type,Args,_) :-
        ir_stmt(Stmts),
        (   memberchk(Type, Stmts), 
            throwerr('missing run_initial_stmt for ~p(~p)~n', [Type,Args])
        ;   throwerr('invalid: run_initial_stmt for ~p(~p)~n', [Type,Args])
        ).
        
set_b_written_to(R) :-
        assert(b_written_to(R)).

