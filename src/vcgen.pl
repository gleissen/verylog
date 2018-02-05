%% #############################################################################
%% ### VERIFICATION CONDITION GENERATION #######################################
%% #############################################################################

:- module(vcgen, [mk_vcs/1], [hidden(true)]).

:- use_module(library(lists)).

:- use_module('lib/misc.pl').
:- use_module('lib/ir.pl').

mk_vcs(Res) :-
        mk_vcs_init(InvInit),
        mk_vcs_main(InvMain),
        format_atom('~p~n~n~p', [InvInit, InvMain], Res).

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
            mk_vc_sep(_R1,R1)
        ),

        get_tag_vars(TagVars),
        exclude(contains(SourceTagVars), TagVars, RestVars),
        (   foreach(TV2, RestVars),
            foreach(R2,  TVRes2),
            param(TVRes2)
        do  mk_lhs_name(TV2, TVL2),
            mk_rhs_name(TV2, TVR2),
            format_atom('~p = 0, ~p = 0', [TVL2, TVR2], _R2),
            mk_vc_sep(_R2,R2)
        ),

        get_other_vars(OtherVars),
        (   foreach(TV3, OtherVars),
            foreach(R3,  TVRes3),
            param(TVRes3)
        do  mk_lhs_name(TV3, TVL3),
            mk_rhs_name(TV3, TVR3),
            format_atom('~p = 0, ~p = 0', [TVL3, TVR3], _R3),
            mk_vc_sep(_R3,R3)
        ),

        (   foreach(S, Sources),
            foreach(R,  TVRes4),
            param(TVRes4)
        do  dot([mk_lhs_name, mk_var_name], S, VL),
            dot([mk_rhs_name, mk_var_name], S, VR),
            format_atom('~p = ~p', [VL, VR], _R),
            mk_vc_sep(_R,R)
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

        mk_property(Prop),

	format_atom('inv(~p) :- ~n(~n~p~n;~n~p~n),~n~p.~n~n~p',
                    [VcsArgs, ResNewBit, ResNextStep, ResInv, Prop],
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

        findall(C, ir:cond_atom(C), CondAtoms),
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

mk_property(Res) :-
        done_var(Done),
        maplist(flip(Done), [mk_lhs_name, mk_rhs_name], [DoneL, DoneR]),
        mk_vcs_vars(Vs),
        mk_and(Vs,VsAnd),
        format_atom('~p = 1 :-~ninv(~p), ~p = 1.', [DoneR,VsAnd, DoneL], Res).
        
mk_vc_sep(P,Res) :-
        format_atom('~n  ~p', [P], Res).
