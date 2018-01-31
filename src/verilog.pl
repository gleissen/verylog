:- discontiguous small/1.

:- use_module('lib/misc.pl', [format_atom/3,
			      get_fresh_num/1,
			      mk_and/2,
			      mk_and/3,
                              mk_sum/2
                              ]).

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
        mk_invariant_vars(Vs),
        maplist(mk_atom_name, Vs, _VsAtoms),
        (   foreach(V,_VsAtoms),
            foreach(V1,VsAtoms)
        do  ( atom_chars(V, ['v', '_', 'V', '_', 'v', '_'|_]) -> sub_atom(V,4,_,0,V1)
            ; V1 = V
            )
        ),
        mk_and(VsAtoms,And),
        format_atom('query_naming(inv(~p)).', [And], Res).


%% #############################################################################
%% ### TRANSITION RELATION #####################################################
%% #############################################################################

mk_next(Res) :-
        mk_next_helper_predicates(Helper),
	mk_next_def(Hd),

        mk_next_always(_Always),
        mk_next_sep(_Always,Always),

        mk_next_module_inst(_Module),
        mk_next_sep(_Module,Module),

	mk_next_sink_cond(_Sink),
        mk_next_sep(_Sink,Sink),

        mk_next_incr(_Incr),
        mk_next_sep(_Incr,Incr),

	format_atom(
                    '~p~p :=~n(~p, ~p,~n~n~p,~n~p~n).',
                    [Helper, Hd, Always, Module, Sink, Incr],
                    Res
                   ),
        true.

mk_next_helper_predicates(Res) :-
        HelperPredicates = [ mk_next_helper_assign_op ],
        (   foreach(P, HelperPredicates),
            foreach(R, Rs),
            param(Rs)
        do  current_predicate(P,F),
            functor(F,N,1),
            call(N,_R),
            format_atom('~p~n~n', [_R], R)
        ),
        mk_and(Rs,Res).
        

%% generate the header for the transition relation definition
%% i.e. next(...)
mk_next_def(Res) :-
	mk_invariant_vars(Vs),
	mk_and(Vs,VsAnd),
	format_atom('next(~p)', [VsAnd], Res).

%% update done if sink's tag > 0
%% ite(sink_t >= 1, Done1 = 1, Done1 = Done)
mk_next_sink_cond(Res) :-
        ( taint_sink(_Sink) -> 
            mk_tagvar_name(_Sink, Sink), mk_primed(Sink,Sink1),
            done_var(Done), mk_primed(Done,Done1),
            format_atom('ite(~p >= 1, ~p = 1, ~p = ~p)',[Sink1, Done1, Done1, Done], Res)
        ; print('no taink_sink predicate !'), halt(1)
        ).

%% generates the line for 'Done = 0, T1 = T + 1'
mk_next_incr(Res) :-
        done_var(Done), t_var(T), mk_primed(T,T1),
        format_atom('~p = 0, ~p = ~p + 1', [Done, T1, T], Res).

%% generate the TR for the statements inside the always blocks
mk_next_always(Res) :-
        query_ir(always, Stmts),
        (   foreach(_-Stmt, Stmts),
            foreach(StmtRes,AllStmtRes),
            param(AllStmtRes)
        do  mk_next_stmt(Stmt,_StmtRes),
            mk_next_sep(_StmtRes, StmtRes)
        ),
        maplist(mk_next_sep,AllStmtRes,_Res),
        mk_and(_Res,Res).

%% generate the TR for the statement of the format Type(Args...)
mk_next_stmt(Stmt,Res) :-
        (   Stmt =.. [Type|Args] ->
            ( ir_stmt(L), memberchk(Type, L) -> true
            ; format('~p is not a valid statement !~n', [Type]), halt(1)
            ),
            mk_next_stmt_helper(Type,Args,Res)
        ;   format('~p is not a valid statement !', [Stmt]),
            halt(1)
        ).

%% generate the TR for process a non-blocking assignment
mk_next_stmt_helper(nb_asn, [L,R], Res) :-
        mk_next_assign_op(L,R,Res).

%% generate the TR for an if statement
mk_next_stmt_helper(ite, [Cond, Then, Else], Res) :-
        mk_next_ite_cond(Cond,CondT,CondF),
        mk_next_stmt(Then, ThenRes),
        mk_next_stmt(Else, ElseRes),
        format_atom('((~p) -> (~p) ; (~p) -> (~p))', [CondT, ThenRes, CondF, ElseRes], Res).

mk_next_stmt_helper(Type, _, _) :-
        format('~p is not yet implemented~n', [Type]), halt(1).

mk_next_ite_cond(Cond, ResT, ResF) :-
        (   \+ atom(Cond) ->
            format('only atomic if conditions are supported (i.e. not ~p))', [Cond]),
            halt(1)
        ;   mk_var_name(Cond,CondV),
            format_atom('~p >= 1', [CondV], ResT),
            format_atom('~p  = 0', [CondV], ResF)
        ).

%% generate the TR for a module instantiation
mk_next_module_inst(Res) :-
        query_ir(module_inst, Modules),
        maplist(mk_next_module_helper, Modules, Ms),
        maplist(mk_next_sep, Ms, Ms2),
        mk_and(Ms2,Res).

mk_next_module_helper(_Name-Inputs-Outputs,Res) :-
        maplist(mk_tagvar_name,Inputs,InputVars),
        (   foreach(O, Outputs),
            foreach(R, Rs),
            param(Inputs)
        do  mk_sum(InputVars, Rhs),
            mk_tagvarprimed_name(O, Lhs),
            format_atom('~p = ~p', [Lhs, Rhs], _R),
            mk_next_sep(_R,R)
        ),
        mk_and(Rs,Res).

mk_next_assign_op(L,R,Res) :-
        !,
        mk_var_name(L,LV), mk_primed(LV,LV1),
        mk_var_name(R,RV),
        mk_tagvar_name(L,LT), mk_primed(LT,LT1),
        mk_tagvar_name(R,RT),
        format_atom('assign_op(~p, ~p, ~p, ~p)', [LT1, RT, LV1, RV], Res).

mk_next_helper_assign_op(Res) :-
        format_atom('assign_op(LT1, RT, LV1, RV) :- !, LT1 = RT, LV1 = RV.', [], Res).
        
mk_next_sep(P,Res) :-
        format_atom('~n  ~p', [P], Res).

%% #############################################################################
%% ### INVARIANTS ##############################################################
%% #############################################################################

mk_invariant_vars(Vs) :-
        mk_invariant_vars_helper(Vars),
        maplist(mk_primed, Vars, Vars1),
        append(Vars,Vars1,Vs).

mk_invariant_vars_helper(VsAllVars) :-
        query_ir(register,VsRegs),
        maplist(mk_var_name,VsRegs,VsRegVars),
        maplist(mk_tag_name,VsRegVars,VsRegVarsT),
        append(VsRegVars,VsRegVarsT,VsMostVars),
        done_var(Done),
        t_var(T),
        append(VsMostVars, [Done, T], VsAllVars).

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
	format('~p',[Res]).
        
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

ir_stmt([
         nb_asn,
         ite
        ]).

ir_list([
         register, wire, module_inst, always,
         taint_source, taint_sink
        ]).

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

mk_tag_name(ID, VarName) :-
        add_suffix('_t', ID, VarName).

mk_tagvar_name(ID, TagVarName) :-
        dot([mk_var_name, mk_tag_name], ID, TagVarName).

mk_tagvarprimed_name(ID, TagVarName) :-
        dot([mk_primed, mk_var_name, mk_tag_name], ID, TagVarName).

mk_atom_name(ID, AtomName) :-
        add_prefix('v_', ID, AtomName).

mk_primed(X,X1) :-
        add_suffix('1', X, X1).

mk_ite(Cond,Then,Else,Res) :-
        format_atom('ite(~p, ~p, ~p)', [Cond, Then, Else], Res).

missing_atom(P, Res) :-
        inline_comment(P, Comment),
        format_atom('~p true', [Comment], Res).

inline_comment(P, Comment) :-
        atom_codes(CB, "/*"),
        atom_codes(CE, "*/"),
        format_atom('~p ~p ~p', [CB, P, CE], Comment).

dot([],In,In).
dot([H|T],In,Out) :-
        dot(T, In, _Out),
        current_predicate(H,F),
        functor(F,N,2),
        call(N, _Out, Out).

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

