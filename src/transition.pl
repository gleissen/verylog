%% #############################################################################
%% ### TRANSITION RELATION #####################################################
%% #############################################################################

:- module(transition, [mk_next/1], [hidden(true)]).

:- use_module(library(lists)).

:- use_module('lib/misc.pl').
:- use_module('lib/ir.pl').

mk_next(Res) :-
        mk_next_helper_predicates(Helper),
	mk_next_def(Hd),

        ir_toplevel_list(_TLPs),
        SkippedToplevels = [register, wire, taint_source, link],
        exclude(contains(SkippedToplevels), _TLPs, TLPs),
        maplist(dot([transition:mk_next_sep, transition:mk_next_toplevel]), TLPs, Rs),
        mk_and(Rs,RsAnd),

        mk_next_incr(_Incr),
        mk_next_sep(_Incr,Incr),

	format_atom('~p~p :=~n(~p,~p~n).', [Helper, Hd, RsAnd, Incr], Res).

mk_next_toplevel(always, Res)        :- !, mk_next_always(Res).
mk_next_toplevel(module_inst, Res)   :- !, mk_next_module_inst(Res).
mk_next_toplevel(taint_sink, Res)    :- !, mk_next_sink_cond(Res).
mk_next_toplevel(asn, Res)           :- !, mk_next_asn(Res).
mk_next_toplevel(TLP, _) :-
        throwerr('mk_next_toplevel for ~p is not yet implemented !', [TLP]).

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
        ( ir:taint_sink(_Sink) -> 
            mk_tagvar_name(_Sink, Sink), mk_primed(Sink,Sink1),
            done_var(Done), mk_primed(Done,Done1),
            inline_comment('sink statement', Comment),
            format_atom('~p ite(~p >= 1, ~p = 1, ~p = ~p)',[Comment, Sink1, Done1, Done1, Done], Res)
        ; throwerr('no taink_sink predicate !', [])
        ).

%% generates the line for 'Done = 0'
mk_next_incr(Res) :-
        done_var(Done),
        format_atom('~p = 0', [Done], Res).

mk_next_asn(Res) :-
        query_ir(asn, Asns),
        (   foreach(Lhs-Rhs, Asns),
            foreach(R, Rs),
            param(Rs)
        do  mk_next_assign_op(Lhs,Rhs,_R),
            mk_next_sep(_R,R)
        ),
        mk_and(Rs,Res1),
        inline_comment('assign statements', C),
        format_atom('~p ~p', [C, Res1], Res).
        

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
        mk_and(_Res,Res1),
        inline_comment('always blocks', C),
        format_atom('~p ~p', [C, Res1], Res).

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

mk_next_stmt_helper(b_asn, [L,R], Res) :-
        !, mk_next_assign_op(L,R,Res).

%% generate the TR for an if statement
mk_next_stmt_helper(ite, [Cond, Then, Else], Res) :-
        !,
        mk_var_name(Cond, CondVar),
        mk_next_stmt(Then, ThenRes),
        mk_next_stmt(Else, ElseRes),
        format_atom('((~p >= 1), (~p) ; (~p =< 0), (~p))',
                    [CondVar, ThenRes, CondVar, ElseRes],
                    Res).

mk_next_stmt_helper(block, [Stmts], Res) :-
        !,
        (   foreach(S,Stmts),
            foreach(R,Rs),
            param(Rs)
        do  S =.. [Type|Args],
            mk_next_stmt_helper(Type,Args,R)
        ),
        mk_and(Rs,RsAnd),
        format_atom('(~p)', [RsAnd], Res).
            

mk_next_stmt_helper(Type, Args, _) :-
        throwerr('mk_next_stmt_helper for ~p(~p) is not yet implemented~n', [Type, Args]).

%% generate the TR for a module instantiation
mk_next_module_inst(Res) :-
        query_ir(module_inst, Modules),
        maplist(mk_next_module_helper, Modules, Ms),
        maplist(mk_next_sep, Ms, Ms2),
        mk_and(Ms2,Res1),
        inline_comment('module instantiations', C),
        format_atom('~p ~p', [C, Res1], Res).

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
        (   is_uf(R) ->
            ir:link(R,Atoms),
            (   Atoms = [] ->
                missing_atom(R, Res)
            ;   maplist(mk_tagvar_name, Atoms, TagVars),
                mk_tagvarprimed_name(L, LTagVar1),
                mk_sum(TagVars, TagSum),
                format_atom('~p = ~p', [LTagVar1, TagSum], Res)
            )
        ;   R = const_expr ->
            missing_atom(R, Res)
        ;   atom(R) ->
            mk_var_name(L,LV), mk_primed(LV,LV1),
            mk_var_name(R,RV),
            mk_tagvar_name(L,LT), mk_primed(LT,LT1),
            mk_tagvar_name(R,RT),
            format_atom('assign_op(~p, ~p, ~p, ~p)', [LT1, RT, LV1, RV], Res)
        ;   number(R) ->
            missing_atom(R,Res)
        ;   otherwise ->
            throwerr('cannot assign ~p to ~p', [R, L])
        ).

mk_next_helper_assign_op(Res) :-
        format_atom('assign_op(LT1, RT, LV1, RV) :- LT1 = RT, LV1 = RV.', [], Res).
        
mk_next_sep(P,Res) :-
        format_atom('~n  ~p', [P], Res).

