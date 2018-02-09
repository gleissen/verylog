:- use_module(library(lists)).

:- use_module('lib/misc.pl').
:- use_module('lib/ir.pl').

check_race :-
        ir_toplevel_list(TopLevelPredicates),
        (   foreach(P, TopLevelPredicates)
        do  query_ir(P, PInsts),
            maplist(check_toplevels(P), PInsts, _)
        ).

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% TOPLEVEL ELEMENTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_toplevels(always, _Event-Stmt, R) :- !,
        check_stmt_(Stmt, R).

check_toplevels(initial, Stmt, R) :- !,
        check_stmt_(Stmt, R).

check_toplevels(link,_UFOut-_UFIns,_) :- !.

check_toplevels(asn,L-R,_) :- !,
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

check_toplevels(register,_,_) :- !.
check_toplevels(wire,_,_) :- !.
check_toplevels(taint_source,_,_) :- !.
check_toplevels(taint_sink,_,_) :- !.

check_toplevels(TL,P,_) :-
        throwerr('check_toplevels is not yet implemented for ~p as in ~p~n', [TL,P]).

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% STATEMENTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_stmt(ite,[_Cond, Then, Else], _) :- !,
        check_stmt_(Then, _),
        check_stmt_(Else, _).

check_stmt(nb_asn,[_L, _R], _) :- !.

check_stmt(b_asn,[_L, _R], _) :- !.
        
check_stmt(block,[Stmts], _) :- !,
        (   foreach(S, Stmts)
        do  check_stmt_(S,_)
        ).

check_stmt(for, [_Vars], _) :- !.

check_stmt(skip,_,_) :- !.

check_stmt(Type,Args,_) :-
        ir_stmt(Stmts),
        (   memberchk(Type, Stmts) ->
            throwerr('missing check_stmt for ~p(~p)~n', [Type,Args])
        ;   throwerr('invalid: check_stmt for ~p(~p)~n', [Type,Args])
        ).
        
check_stmt_(Stmt, Res) :-
        Stmt =.. [Type|Args],
        check_stmt(Type, Args, Res).

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% OTHER STUFF %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

main :-
        prolog_flag(argv, [Input|_]),
        read_ir(Input),
        check_race,
        format('DONE !~n', []).
