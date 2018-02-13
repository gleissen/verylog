:- use_module(library(lists)).

:- use_module('lib/misc.pl').
:- use_module('lib/ir.pl').

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% CHECK RACE CONDITIONS %%%%%%%%%%%%%%%%%%%%%%%%5%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic db_ca/2, db_nba/2, db_ba/2.

wipe_db :-
        retractall(db_ca(_,_)),
        retractall(db_nba(_,_)),
        retractall(db_ba(_,_)).

:- wipe_db.

has_race(As, Race) :-
        flatten(As,As1),
        pr(As1),
        wipe_db,
        has_race_helper(As1, Race).

has_race_helper([], _) :- false.

has_race_helper([ba(X,Y)|T], R) :-
        (   db_ba(X,Z) ->
            format_atom('~p := ~p AND ~p := ~p', [X,Y,X,Z], R)
        ;   db_ba(Z,X) ->
            format_atom('~p := ~p AND ~p := ~p', [X,Y,Z,X], R)
        ;   db_nba(Z,X) ->
            format_atom('~p := ~p AND ~p <= ~p', [X,Y,Z,X], R)
        ;   otherwise ->
            assert(db_ba(X,Y)),
            has_race_helper(T, R)
        ).

has_race_helper([nba(X,Y)|T], R) :-
        (   db_nba(X,Z) ->
            format_atom('~p <= ~p AND ~p <= ~p', [X,Y,X,Z], R)
        ;   db_ba(Y,Z) ->
            format_atom('~p <= ~p AND ~p := ~p', [X,Y,Y,Z], R)
        ;   otherwise ->
            assert(db_nba(X,Y)),
            has_race_helper(T, R)
        ).

has_race_helper([ca(X,Y)|T], R) :-
        warn('skipping cont. asgn. ~p = ~p', [X,Y]),
        assert(db_ca(X,Y)),
        has_race_helper(T, R).

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% GATHER ASSIGN STATEMENTS AS ca, nba and ba %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

gather_stmts(AssignStmts) :- !,
        findall(X1-Y1, ir:asn(X1,Y1), Asgns),
        maplist(check_cont_assigns, Asgns, CAs),
        
        findall(S, ir:always(_,S), AlwaysBlocks),
        maplist(gather_always_stmts, AlwaysBlocks, As),

        append(CAs, As, AssignStmts).

gather_always_stmts(Stmt, As) :-
        gather_stmt_(Stmt, As).

check_cont_assigns(L-R, Asn) :- mk_asgn(ca, L, R, Asn).

gather_stmt(ite,[_, Then, _Else], Stmt1) :- gather_stmt_(Then, Stmt1).
gather_stmt(ite,[_, _Then, Else], Stmt1) :- gather_stmt_(Else, Stmt1).

gather_stmt(nb_asn, [L, R], Asn) :- mk_asgn(nba, L, R, Asn).
gather_stmt(b_asn,  [L, R], Asn) :- mk_asgn(ba,  L, R, Asn).

gather_stmt(block,[Stmts], As) :-
        maplist(gather_stmt_, Stmts, _As),
        flatten(_As, As).

gather_stmt(skip,_,[]).

gather_stmt_(Stmt, Res) :-
        Stmt =.. [Type|Args],
        gather_stmt(Type, Args, Res).

mk_asgn(Type, L, R, Asn) :-
        _Asn =.. [Type,L,R],
        (   is_uf(R) ->
            ir:link(R,Rs),
            maplist(mk_asgn(Type,L),Rs,Asns),
            flatten(Asns,Asn)
        ;   otherwise ->
            Asn = [_Asn]
        ).

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% MAIN %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

got_race(Race) :-
        prolog_flag(argv, [Input|_]),
        read_ir(Input),
        gather_stmts(As),
        has_race(As, Race).

main :-
        (   got_race(Race) -> 
            warn('~nFollowing Verilog code contains a race condition:~n~p~n', [Race]),
            halt(1)
        ;   halt(0)
        ).

pr(X) :-
        format('~p~n', [X]).
