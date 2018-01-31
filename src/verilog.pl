:- discontiguous small/1.

:- use_module('lib/misc.pl', [format_atom/3,
			      get_fresh_num/1,
			      mk_and/2,
			      mk_and/3]).

:- use_module('lib/utils.pl').
:- use_module(library(lists)).
:- use_module(library(file_systems)).

/*
==========================================
Clauses used in the intermediate language:
==========================================
register(R)
wire(W)
link(InstName, InputArgs, OutputArgs)
always(Event, Statement)
taint_source(R)
taint_sink(R)
nb_asn(Lhs,Rhs)
*/

/*
Creates Horn clause verification conditions from a intermediate language verilog file.
*/

%% #############################################################################
%% ### INITIAL STATES AND PROPERTY #############################################
%% #############################################################################

%% prints the query_naming predicated required by qarmc
%% i.e. query_naming(inv(...)).
mk_query_naming(Res) :-
        query_ir(register,_Rs),
        done_atom(Done),
        t_atom(T),
        append(_Rs,[Done,T],Rs),
        (   foreach(S, ['l', 'r']),
            foreach(And, Ands),
            param(Rs)
        do  maplist(add_suffix(S), Rs, Rs1),
            mk_and(Rs1, And)
        ),
        [And1, And2] = Ands,
	format_atom('query_naming(inv(~n    ~p,~n    ~p~n)).', [And1, And2], Res).

% mk_init(Res) :-
% 	mk_invariant_vars('L=0', DefsL),
% 	mk_invariant_vars('R=0', DefsR),
% 	mk_and(DefsL, DefsL1),
% 	mk_and(DefsR, DefsR1),
% 	format_atom('~p,DoneL = 0, ~p, DoneR=0.',[DefsL1,DefsR1], Res).

% mk_property(Res) :-
% 	mk_relational_invariant(Inv),
% 	format_atom('DoneR=1 :- ~p, DoneL=1.', [Inv], Res).


% mk_vcs(Res) :-
% 	mk_init(Init),
% 	mk_relational_invariant(Inv),
% 	mk_primed_relational_invariant(Inv1),
% 	mk_next_def('L', NextL),
% 	mk_next_def('R', NextR),
% 	mk_property(Prop),
% 	format_atom('~p:-~p~n~p :- ~p,~n~p,~n~p.~n~p~n',[Inv,Init,Inv1,NextL,NextR,Inv,Prop], Res).

%% #############################################################################
%% ### TRANSITION RELATION #####################################################
%% #############################################################################

mk_next(Res) :-
	% mk_assignments(Asn),
	% mk_links(Links),
	% % Links=[],
	% mk_and(Asn, Asn1),
	% mk_and(Links, Links1),
	% mk_and(Asn1, Links1, Bd),
	mk_next_def(Hd),
	% mk_reset(Reset),
	mk_next_sink_cond(_Sink), mk_next_sep(_Sink,Sink),
        mk_next_incr(_Incr),      mk_next_sep(_Incr,Incr),
	% mk_unassigned(Un),
	% format_atom('Done=1, T1=T, Done1=Done',[], Spin),
	format_atom(
                    '~p :=~n(~p,~p~n).',
                    [Hd, Sink, Incr],
                    Res
                   ),
	% format_atom('~p := ~n(~n Done=0, ~p~n; Done=0, ~p, ~p,~p~n; ~p~n).',[Hd,Reset,Sink,Un,Bd,Spin], Res),
        true.

%% generate the header for the transition relation definition
%% i.e. next(...)
mk_next_def(Res) :-
	mk_invariant_vars('',  Vs),
	mk_invariant_vars('1', Vs1),
	mk_and(Vs,  VsAnd),
	mk_and(Vs1, VsAnd1),
	format_atom('next(~n    ~p,~n    ~p~n    )', [VsAnd,VsAnd1], Res).

%% update done if sink's tag > 0
%% ite(sink_t >= 1, Done1 = 1, Done1 = Done)
mk_next_sink_cond(Res) :-
        ( taint_sink(_Sink) -> 
            mk_var_name(_Sink, Sink),
            done_var(Done), mk_primed_var(Done,Done1),
            mk_primed_var(Sink,Sink1),
            format_atom('ite(~p >= 1, ~p = 1, ~p = ~p)',[Sink1, Done1, Done1, Done], Res)
        ; print('no taink_sink predicate !'), halt(1)
        ).

%% generates the line for 'Done = 0, T1 = T + 1'
mk_next_incr(Res) :-
        done_var(Done), t_var(T), mk_primed_var(T,T1),
        format_atom('~p = 0, ~p = ~p + 1', [Done, T1, T], Res).

% mk_assignments(Res) :-
%         query_ir(nb_asn, Ls),
%         (   foreach(X-Y, Ls),
%             foreach(Rel, Res)
%         do  mk_var_name(X, XV),
%             mk_var_name(Y, YV),
%             assert(assigned(Y)),
%             format_atom("~p=~p1",[XV,YV], Rel)
%         ).

% mk_links(Res) :-
%         query_ir(link, Ls),
% 	(   foreach(X-Y-Z, Ls),
% 	    foreach(Rel, Res)
% 	do  mk_var_name(X, XV),
% 	    mk_var_name(Y, YV),
% 	    mk_var_name(Z, ZV),
% 	    assert(assigned(Z)),
% 	    format_atom("ite((~p=1; ~p=1), ~p1=1, ~p1=0)",[XV,YV,ZV,ZV], Rel)
% 	).

% mk_unassigned(Res) :-
% 	findall(X, (query_ir(register,Rs), memberchk(X, Rs), \+assigned(X)), Vs),
% 	(   foreach(V, Vs),
% 	    foreach(Def, Defs)
% 	do  mk_var_name(V, VN),
% 	    format_atom('~p1=0',[VN], Def)
% 	),
% 	mk_and(Defs, Res).

% mk_reset(Res) :-
%         query_ir(register,Vs),
% 	(   foreach(V, Vs),
% 	    fromto('', In, Out, Defs)
% 	do  mk_var_name(V, VN),
% 	    (   taint_source(V)->
% 		format_atom('~p (~p1=1;~p1=0), ',[In,VN,VN], Out)
% 	    ;   format_atom('~p ~p1=0, ',[In,VN], Out)
% 	    )
% 	),
% 	format_atom('~p Done1=0', [Defs], Res).

mk_next_sep(P,Res) :-
        format_atom('~n  ~p', [P], Res).

%% #############################################################################
%% ### INVARIANTS ##############################################################
%% #############################################################################

mk_invariant_vars(Suffix, Vs1) :-
        query_ir(register,__Vs),
        maplist(mk_var_name, __Vs, _Vs),
        done_var(Done),
        t_var(T),
        append(_Vs, [Done, T], Vs),
	(   foreach(V, Vs),
	    foreach(V1, Vs1),
	    param(Suffix)
	do format_atom('~p~p', [V, Suffix], V1)
	).

% mk_invariant(Suffix, Res) :-
% 	mk_invariant_vars(Suffix, Vs1),
% 	mk_and(Vs1, Vs2),  
% 	format_atom('inv(~p, Done~p, T~p)', [Vs2, Suffix, Suffix], Res).

% mk_invariant(Res) :-
% 	mk_invariant('', Res).

% mk_primed_invariant(Res) :-
% 	mk_invariant('1', Res).

% mk_relational_invariant(Res) :-
% 	mk_relational_invariant('',Res).

% mk_primed_relational_invariant(Res) :-
% 	mk_relational_invariant('1', Res).

% mk_relational_invariant(Suffix, Res) :-
% 	format_atom('L~p', [Suffix], SuffixL),
% 	format_atom('R~p', [Suffix], SuffixR),
% 	mk_invariant_vars(SuffixL, VLs),
% 	mk_invariant_vars(SuffixR, VRs),
% 	format_atom('DoneL~p', [Suffix], DoneL),
% 	format_atom('DoneR~p', [Suffix], DoneR),
% 	append([DoneR|VRs], [DoneL|VLs], V1s),
% 	mk_and(V1s, Vs2),  
% 	format_atom('inv(~p)', [Vs2], Res).



%% #############################################################################
%% ### RUNNING #################################################################
%% #############################################################################

mk_output_file(Res) :-
        % Res0 = '',
	mk_query_naming(Naming),
        format_atom('~p', [Naming], Res0),

        % Res1 = '',
	mk_next(Next),
        format_atom('~p', [Next], Res1),

        Res2 = '',
	% mk_vcs(Vcs),
        % format_atom('~p', [Vcs], Res2),

        format_atom('~n~n~p~n~n~p~n~n~p', [Res0, Res1, Res2], Res),
        true.
	
main :-
        prolog_flag(argv, [Input|_]),
        runInput(Input).

runInput(Input) :-
        % print_file(Input),
        my_consult(Input),

	mk_output_file(Res),

	format('~p',[Res]),
        true.
        
my_consult(File) :-
        % flush_db,
        consult(File),
        (current_predicate(parse_failed/1) -> halt(1); true),
        true.

user:runtime_entry(start) :-
        main.

test :-
        % current_directory(Dir), print(Dir),
        runInput(['../examples/verilog/.stall.pl']).

%% #############################################################################
%% ### UTILITY PREDICATES ######################################################
%% #############################################################################

ir_list(L) :- L = [register, wire, link, always,
                   nb_asn,
                   taint_source, taint_sink].

done_var('Done').
done_atom('done').

t_var('T').
t_atom('t').

query_ir(P, Ls) :-
        ( findall(F, current_predicate(P,F), Fs), length(Fs, N), N > 1 ->
            format('~p has multiple arities !', [P]), halt(1)
        ; ir_list(IR), \+ memberchk(P, IR) ->
            format('~p does not belong to the IR !', [P]), halt(1)
        ; true
        ),                      % sanity check
        ( current_predicate(P,F), functor(F,N,A)  ->
            ( A = 1 -> findall(X,     call(N,X),     Ls)
            ; A = 2 -> findall(X-Y,   call(N,X,Y),   Ls)
            ; A = 3 -> findall(X-Y-Z, call(N,X,Y,Z), Ls)
            ; (format('Unknown predicate in query: ~p~n', [P]), halt(1))
            )
        ; Ls=[]
        ).

add_suffix(S,X,X1) :-
        format_atom('~p~p', [X,S], X1).

add_prefix(P,X,X1) :-
        format_atom('~p~p', [P,X], X1).

mk_var_name(ID, VarName) :-
        add_prefix('V_', ID, VarName).

mk_primed_var(X,X1) :-
        add_suffix('1', X, X1).

mk_ite(Cond,Then,Else,Res) :-
        format_atom('ite(~p, ~p, ~p)', [Cond, Then, Else], Res).
