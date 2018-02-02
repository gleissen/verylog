:- discontiguous small/1.

:- use_module('lib/misc.pl', [format_atom/3,
			      get_fresh_num/1,
			      mk_and/2,
			      mk_and/3,
                              mk_sum/2,
                              contains/2,
                              flatten/2,
                              throwerr/2,
                              warn/2
                              ]).

:- use_module('lib/utils.pl').
:- use_module(library(lists)).
:- use_module(library(file_systems)).

:- dynamic
        cond_atoms/1,
        ite/4
        .

:-
        retractall(cond_atoms(_)),
        retractall(ite(_,_,_,_)).
        

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
        assert(ite(Id,Cond,Then,Else)),
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
        

%% #############################################################################
%% ### INITIAL STATES AND PROPERTY #############################################
%% #############################################################################

%% prints the query_naming predicated required by qarmc
%% i.e. query_naming(inv(...)).
mk_query_naming(Res) :-
        mk_vcs_vars(Vs),
        maplist(mk_atom_name, Vs, _VsAtoms),
        (   foreach(V, _VsAtoms),
            foreach(V1, VsAtoms),
            param(VsAtoms)
        do  (   atom_chars(V, ['v', '_', 'V', '_', 'v', '_'|_]) ->
                sub_atom(V,4,_,0,V1)
            ;   V1 = V
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
                    '~p~p :=~n(~p,~p,~p,~p~n).',
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
        ; throwerr('no taink_sink predicate !', [])
        ).

%% generates the line for 'Done = 0, T1 = T + 1'
mk_next_incr(Res) :-
        done_var(Done),
        format_atom('~p = 0', [Done], Res).

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
            ; throwerr('~p is not a valid statement !~n', [Type])
            ),
            mk_next_stmt_helper(Type,Args,Res)
        ;   throwerr('~p is not a valid statement !', [Stmt])
        ).

%% generate the TR for process a non-blocking assignment
mk_next_stmt_helper(nb_asn, [L,R], Res) :-
        !, mk_next_assign_op(L,R,Res).

%% generate the TR for an if statement
mk_next_stmt_helper(ite, [Id, _Cond, Then, Else], Res) :-
        !,
        (   atom(_Cond) -> mk_var_name(_Cond,Cond)
        ;   throwerr('non-atom condition is not yet supported in ite(~p,~p,~p,~p)', [Id, _Cond, Then, Else])
        ),
        % mk_ite_cond_var(Id, CondTempVar),
        mk_next_stmt(Then, ThenRes),
        mk_next_stmt(Else, ElseRes),
        format_atom('((~p >= 1), (~p) ; (~p =< 0), (~p))', [Cond, ThenRes, Cond, ElseRes], Res).

mk_next_stmt_helper(Type, Args, _) :-
        throwerr('~p(~p) is not yet implemented~n', [Type, Args]).

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
        format_atom('assign_op(LT1, RT, LV1, RV) :- LT1 = RT, LV1 = RV.', [], Res).
        
mk_next_sep(P,Res) :-
        format_atom('~n  ~p', [P], Res).

mk_next_vars(Vs) :-
        get_all_vars(Vars),
        mk_next_vars(Vars,Vs).

mk_next_vars(Vars,Vs) :-
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
        (   foreach(TV1, SourceTagVars),
            foreach(R1, TVRes1),
            param(TVRes1)
        do  mk_lhs_name(TV1, TVL1),
            mk_rhs_name(TV1, TVR1),
            format_atom('~p = 1, ~p = 1', [TVL1, TVR1], _R1),
            mk_next_sep(_R1,R1)
        ),

        get_tag_vars(TagVars),
        exclude(contains(SourceTagVars), TagVars, RestVars),
        (   foreach(TV2, RestVars),
            foreach(R2,  TVRes2),
            param(TVRes2)
        do  mk_lhs_name(TV2, TVL2),
            mk_rhs_name(TV2, TVR2),
            format_atom('~p = 0, ~p = 0', [TVL2, TVR2], _R2),
            mk_next_sep(_R2,R2)
        ),

        get_other_vars(OtherVars),
        (   foreach(TV3, OtherVars),
            foreach(R3,  TVRes3),
            param(TVRes3)
        do  mk_lhs_name(TV3, TVL3),
            mk_rhs_name(TV3, TVR3),
            format_atom('~p = 0, ~p = 0', [TVL3, TVR3], _R3),
            mk_next_sep(_R3,R3)
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
	mk_vcs_vars(_VcsVars),
        maplist(mk_primed,_VcsVars,VcsVars),
	mk_and(VcsVars,VcsArgs),

        mk_vcs_main_issue_new_bit(ResNewBit),
        mk_vcs_main_next_step(ResNextStep),
        mk_vcs_main_given_inv(ResInv),

	format_atom('inv(~p) :- ~n(~n~p~n;~n~p~n),~n~p.',
                    [VcsArgs, ResNewBit, ResNextStep, ResInv],
                    Res
                   ).

mk_vcs_main_issue_new_bit(Res) :-
        %% both executions have not finished yet
        done_var(Done),
        maplist(flip(Done), [mk_lhs_name,mk_rhs_name], [DoneL, DoneR]),
        maplist(mk_primed,   [DoneL,DoneR], [DoneL1,DoneR1]),
        format_atom('~p = 0, ~p = 0', [DoneL, DoneL1], Line1),
        format_atom('~p = 0, ~p = 0', [DoneR, DoneR1], Line2),

        %% issue a new taint bit
        query_ir(taint_source, Sources),
        maplist(dot([mk_lhs_name, mk_tagvar_name]), Sources, SourceTagLeftVars),
        maplist(dot([mk_rhs_name, mk_tagvar_name]), Sources, SourceTagRightVars),
        append(SourceTagLeftVars, SourceTagRightVars, SourceTagVars),
        (   foreach(STV, SourceTagVars),
            foreach(R1, Line3),
            param(Line3)
        do  mk_primed(STV, STV1),
            format_atom('~p = 1', [STV1], R1)
        ),
        mk_and(Line3,Line3And),

        %% all variable valuations stay the same.
        mk_vcs_vars(VcsVars),
        exclude(contains([DoneL,DoneR|SourceTagVars]), VcsVars, RestVars),
        (   foreach(V, RestVars),
            foreach(V2, Line4)
        do  mk_primed(V,V1),
            format_atom('~p = ~p', [V1, V], V2)
        ),
        mk_and(Line4,Line4And),
        
        format_atom('~p,~n~p,~n~p,~n~p',
                    [Line1,Line2,Line3And,Line4And],
                    Res).

%% both not done: both executions take a step.
mk_vcs_main_next_step(Res) :-
        get_all_vars(AllVars),

        maplist(mk_lhs_name, AllVars, LeftVars),
        mk_next_vars(LeftVars,NextVarsLeft),
        mk_and(NextVarsLeft, NextVarsLeftAnd),

        maplist(mk_rhs_name, AllVars, RightVars),
        mk_next_vars(RightVars,NextVarsRight),
        mk_and(NextVarsRight, NextVarsRightAnd),

        %% TODO: fix this hack
        %% get_cond_vars(CondVars),
        findall(C, ite(_Id,C,_Then,_Else), CondAtoms),
        maplist(mk_var_name,CondAtoms,CondVars),
        (   foreach(CV, CondVars),
            foreach(CE, CES),
            param(CES)
        do  maplist(flip(CV), [mk_lhs_name, mk_rhs_name], [CVL, CVR]),
            format_atom('~p = ~p', [CVL,CVR], CE)
        ),
        mk_and(CES,CondEqualities),

        %% both read same instructions
        query_ir(taint_source, Sources),
        (   foreach(SAtom, Sources),
            foreach(SI, SIS),
            param(SIS)
        do  mk_var_name(SAtom, SVar),
            maplist(dot([mk_primed, flip(SVar)]),
                    [mk_lhs_name, mk_rhs_name],
                    [SVarL1, SVarR1]),
            mk_tag_name(SVar, STVar),
            maplist(dot([mk_primed, flip(STVar)]),
                    [mk_lhs_name, mk_rhs_name],
                    [STVarL1, STVarR1]),
            format_atom('~p = ~p, ~p = 0, ~p = 0', [SVarL1, SVarR1, STVarL1, STVarR1], SI)
        ),
        mk_and(SIS, SameInstructions),

        format_atom('next(~p),~nnext(~p),~n~p,~n~p',
                    [NextVarsLeftAnd, NextVarsRightAnd, CondEqualities, SameInstructions],
                    Res).

mk_vcs_main_given_inv(Res) :-
        mk_vcs_vars(VcsVars),
        mk_and(VcsVars,VcsArgs),
        format_atom('inv(~p)', [VcsArgs], Res).

mk_vcs_vars(Vs) :-
        get_all_vars(AllVars),
        maplist(mk_lhs_name, AllVars, LeftVars),
        maplist(mk_rhs_name, AllVars, RightVars),
        append(LeftVars,RightVars,Vs).

mk_property(Res) :-
        done_var(Done),
        maplist(flip(Done), [mk_lhs_name, mk_rhs_name], [DoneL, DoneR]),
        mk_vcs_vars(Vs),
        mk_and(Vs,VsAnd),
        format_atom('~p = 1 :-~ninv(~p), ~p = 1.', [DoneR,VsAnd, DoneL], Res).
        

%% #############################################################################
%% ### RUNNING #################################################################
%% #############################################################################

mk_output_file(Res) :-
        % Res0 = '',
        % Res1 = '',
        % Res2 = '',
        % Res3 = '',

	mk_query_naming(Naming),
        format_atom('~p', [Naming], Res0),

	mk_next(Next),
        format_atom('~p', [Next], Res1),

	mk_vcs(Vcs),
        format_atom('~p', [Vcs], Res2),

        mk_property(Res3),

        format_atom('~n~n~p~n~n~p~n~n~p~n~n~p', [Res0, Res1, Res2, Res3], Res),
        true.
	
main :-
        prolog_flag(argv, [Input|_]),
        runInput(Input).

runInput(Input) :-
        % print_file(Input),
        my_consult(Input),
        run_initial_pass,
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
        current_directory(Dir), print(Dir),
        % Input = '../examples/verilog/.stall.pl',
        Input = '../../../papers/risc-timing/examples/.472-mips-fragment.pl',
        print(Input),
        runInput([Input]).

%% #############################################################################
%% ### UTILITY PREDICATES ######################################################
%% #############################################################################

ir_stmt([
         block,
         n_asn,
         nb_asn,
         ite
        ]).

ir_toplevel_list([
                  register, wire, module_inst, always,
                  link, asn,
                  taint_source, taint_sink
                 ]).

done_var('Done').
done_atom('done').

query_ir(P, Ls) :-
        ( findall(F, current_predicate(P,F), [_,_|_]) ->
            throwerr('~p has multiple arities !', [P])
        ; ir_toplevel_list(IR), \+ memberchk(P, IR) ->
            throwerr('~p does not belong to the IR !', [P])
        ; true
        ),                      % sanity check
        ( current_predicate(P,F), functor(F,N,A)  ->
            ( A = 1 -> findall(X,     call(N,X),     Ls)
            ; A = 2 -> findall(X-Y,   call(N,X,Y),   Ls)
            ; A = 3 -> findall(X-Y-Z, call(N,X,Y,Z), Ls)
            ; throwerr('Unknown predicate in query: ~p~n', [P])
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

mk_ite_cond_atom(Id, Cond) :-
        format_atom('cond_~p_', [Id], Cond).

mk_ite_cond_var(Id, Cond) :-
        dot([mk_var_name, mk_ite_cond_atom], Id, Cond).

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

get_cond_vars(Conds) :-
        findall(X, cond_atoms(X), _CondAtoms),
        remove_dups(_CondAtoms,CondAtoms),
        maplist(mk_var_name,CondAtoms,Conds).

get_other_vars([Done|Conds]) :-
        done_var(Done),
        get_cond_vars(Conds).

get_all_vars(VsAllVars) :-
        get_reg_vars(VsRegVars),
        get_tag_vars(VsTagVars),
        get_other_vars(VsOtherVars),
        flatten([VsRegVars,VsTagVars,VsOtherVars], VsAllVars).

fold(_,A,[],A) :- !.
fold(P,A,[H|T],R) :-
        !,
        call(P,A,H,A2),
        fold(P,A2,T,R).

fold(_,_,T,_) :-
        throwerr('~n!!! fold for ~p is not yet implemented !!!~n', [T]).

flip(A,F,R) :- call(F,A,R).


