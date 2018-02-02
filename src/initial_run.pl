:- module(initial_run, [run_initial_pass/0], [hidden(true)]).

:- use_module(library(lists)).

:- use_module('lib/ir.pl').

%% #############################################################################
%% ### INITIAL PASS OVER THE PROGRAM ###########################################
%% #############################################################################


run_initial_pass :-
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
run_initial_toplevels(asn,_Lhs-_Rhs,_) :- !.

run_initial_toplevels(register,_,_) :- !.
run_initial_toplevels(wire,_,_) :- !.
run_initial_toplevels(taint_source,_,_) :- !.
run_initial_toplevels(taint_sink,_,_) :- !.

run_initial_toplevels(TL,P,_) :-
        throwerr('run_initial_toplevels is not yet implemented for ~p as in ~p~n', [TL,P]).

run_initial_stmt(ite,[Id,Cond,Then,Else], _) :-
        !,
        save(ite(Id,Cond,Then,Else)),
        ( \+ atom(Then)
        ; Then =.. [TypeThen|ArgThen], run_initial_stmt(TypeThen, ArgThen,_)
        ),
        ( \+ atom(Else)
        ; Else =.. [TypeElse|ArgElse], run_initial_stmt(TypeElse, ArgElse,_)
        ).

run_initial_stmt(nb_asn,[_Lhs,_Rhs], _) :- !.

run_initial_stmt(block,[Stmts], _) :- !,
        (   foreach(Stmt, Stmts)
        do  Stmt =.. [Type|Args],
            run_initial_stmt(Type,Args,_)
        ).

run_initial_stmt(Type,Args,_) :-
        ir_stmt(Stmts),
        (   memberchk(Type, Stmts), 
            throwerr('missing run_initial_stmt for ~p(~p)~n', [Type,Args])
        ;   throwerr('invalid: run_initial_stmt for ~p(~p)~n', [Type,Args])
        ).
        
