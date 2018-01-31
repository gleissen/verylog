:- discontiguous small/1.

:- use_module('lib/misc.pl', [format_atom/3,
			      get_fresh_num/1,
			      mk_and/2,
			      mk_and/3,
                              mk_sum/2,
                              contains/2,
                              flatten/2
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
        mk_vcs_vars(Vs),
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
        do  call(P,_R),
            format_atom('~p~n~n', [_R], R)
        ),
        mk_and(Rs,Res).
        

%% generate the header for the transition relation definition
%% i.e. next(...)
mk_next_def(Res) :-
	mk_next_vars(Vs),
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
        !, mk_next_assign_op(L,R,Res).

%% generate the TR for an if statement
mk_next_stmt_helper(ite, [Cond, Then, Else], Res) :-
        !, mk_next_ite_cond(Cond,CondT,CondF),
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

%% just updates the tags to the sum of the inputs
mk_next_module_helper(_Name-Inputs-Outputs,Res) :-
        maplist(mk_tagvar_name,Inputs,InputVars),
        (   foreach(O, Outputs),
            foreach(R, Rs),
            param(InputVars)
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

mk_next_vars(Vs) :-
        get_all_vars(Vars),
        maplist(mk_primed, Vars, Vars1),
        append(Vars,Vars1,Vs).
        

%% #############################################################################
%% ### VERIFICATION CONDITION GENERATION #######################################
%% #############################################################################

mk_vcs(Res) :-
        mk_vcs_init(InvInit),
        mk_vcs_main(InvMain),
        format_atom('~p ~n~n~p', [InvInit, InvMain], Res).

mk_vcs_init(Res) :-
	mk_vcs_vars(VcsVars),
	mk_and(VcsVars,VsArgs),

        query_ir(taint_source, Sources),
        maplist(mk_tagvar_name, Sources, SourceTagVars),
        (   foreach(TV, SourceTagVars),
            foreach(R, TVRes1),
            param(TVRes1)
        do  mk_lhs_name(TV, TVL),
            mk_rhs_name(TV, TVR),
            format_atom('~p = 1, ~p = 1', [TVL, TVR], _R),
            mk_next_sep(_R,R)
        ),

        get_tag_vars(TagVars),
        exclude(contains(SourceTagVars), TagVars, RestVars),
        (   foreach(TV, RestVars),
            foreach(R,  TVRes2),
            param(TVRes2)
        do  mk_lhs_name(TV, TVL),
            mk_rhs_name(TV, TVR),
            format_atom('~p = 0, ~p = 0', [TVL, TVR], _R),
            mk_next_sep(_R,R)
        ),

        get_other_vars(OtherVars),
        (   foreach(TV, OtherVars),
            foreach(R,  TVRes3),
            param(TVRes3)
        do  mk_lhs_name(TV, TVL),
            mk_rhs_name(TV, TVR),
            format_atom('~p = 0, ~p = 0', [TVL, TVR], _R),
            mk_next_sep(_R,R)
        ),

        (   foreach(S, Sources),
            foreach(R,  TVRes4),
            param(TVRes4)
        do  dot([mk_lhs_name, mk_var_name], S, VL),
            dot([mk_rhs_name, mk_var_name], S, VR),
            format_atom('~p = ~p', [VL, VR], _R),
            mk_next_sep(_R,R)
        ),

        flatten([TVRes1, TVRes2, TVRes3, TVRes4], _VsBody),
        mk_and(_VsBody, VsBody),

	format_atom('inv(~p) :- ~p.', [VsArgs, VsBody], Res).

mk_vcs_main(Res) :-
	mk_vcs_vars(VcsVars),
	mk_and(VcsVars,VsArgs),

	format_atom('inv(~p) :- true.', [VsArgs], Res).


mk_vcs_vars(Vs) :-
        get_all_vars(AllVars),
        maplist(mk_lhs_name, AllVars, LeftVars),
        maplist(mk_rhs_name, AllVars, RightVars),
        append(LeftVars,RightVars,Vs).

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

        % Res2 = '',
	mk_vcs(Vcs),
        format_atom('~p', [Vcs], Res2),

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
        ( findall(F, current_predicate(P,F), [_,_|_]) ->
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

mk_lhs_name(ID, VarName) :-
        add_suffix('L', ID, VarName).

mk_rhs_name(ID, VarName) :-
        add_suffix('R', ID, VarName).

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

mk_nl(X,X1) :-
        format_atom('~p~n', [X], X1).

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
        call(H, _Out, Out).

get_reg_vars(VsRegVars) :-
        query_ir(register,VsRegs),
        maplist(mk_var_name,VsRegs,VsRegVars).

get_tag_vars(VsTagVars) :-
        query_ir(register,VsRegs),
        maplist(mk_tagvar_name,VsRegs,VsTagVars).

get_other_vars([Done, T]) :-
        done_var(Done),
        t_var(T).

get_all_vars(VsAllVars) :-
        get_reg_vars(VsRegVars),
        get_tag_vars(VsTagVars),
        get_other_vars(VsOtherVars),
        flatten([VsRegVars,VsTagVars,VsOtherVars], VsAllVars).
