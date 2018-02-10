:- use_module(library(lists)).

:- use_module('lib/misc.pl').
:- use_module('lib/ir.pl').

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% CHECK RACE CONDITIONS %%%%%%%%%%%%%%%%%%%%%%%%5%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

has_race(As, _Race) :-
        pr(As),
        false.

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

check_cont_assigns(L-R, [ca(L,R)]).

gather_stmt(ite,[_, Then, _Else], Stmt1) :- gather_stmt_(Then, Stmt1).
gather_stmt(ite,[_, _Then, Else], Stmt1) :- gather_stmt_(Else, Stmt1).

gather_stmt(nb_asn,[L, R], A) :-
        (   ir:register(L) -> A = [na(L,R)]
        ;   A = []
        ).
            

gather_stmt(b_asn,[L, R], [nba(L,R)]).

gather_stmt(block,[Stmts], As) :-
        maplist(gather_stmt_, Stmts, _As),
        flatten(_As, As).

gather_stmt(skip,_,[]).

gather_stmt_(Stmt, Res) :-
        Stmt =.. [Type|Args],
        gather_stmt(Type, Args, Res).

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
            warn('Following Verilog code contains a race condition:~n~p~n', [Race]),
            halt(1)
        ;   halt(0)
        ).

pr(X) :-
        format('~p~n', [X]).
