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

        %% set taint bits of source registers to 1
        query_ir(taint_source, Sources),
        (   foreach(S, Sources),
            foreach(R1, TVRes1),
            param(TVRes1)
        do  mk_var_name([tag, left],  S, TVL1),
            mk_var_name([tag, right], S, TVR1),
            format_atom('~p = 1, ~p = 1', [TVL1, TVR1], _R1),
            mk_vc_sep(_R1,R1)
        ),

        %% set taint bits of other registers to 0
        findall(R, ir:register(R), Regs),
        exclude(contains(Sources), Regs, RestRegs),
        (   foreach(Reg, RestRegs),
            foreach(R2,  TVRes2),
            param(TVRes2)
        do  mk_var_name([tag, left],  Reg, TVL2),
            mk_var_name([tag, right], Reg, TVR2),
            format_atom('~p = 0, ~p = 0', [TVL2, TVR2], _R2),
            mk_vc_sep(_R2,R2)
        ),

        %% both runs are not done yet
        mk_done_var([left],  DoneL),
        mk_done_var([right], DoneR),
        format_atom('~p=0,~p=0', [DoneL, DoneR], TVRes3),

        %% initial values of the source registers are the same for both runs
        (   foreach(S2, Sources),
            foreach(R4,  TVRes4),
            param(TVRes4)
        do  mk_var_name([left],  S2, VL),
            mk_var_name([right], S2, VR),
            format_atom('~p = ~p', [VL, VR], _R4),
            mk_vc_sep(_R4, R4)
        ),

        flatten([TVRes1, TVRes2, [TVRes3], TVRes4], _VsBody),
        mk_and(_VsBody, VsBody),

	format_atom('inv(~p) :- ~p.', [VsArgs, VsBody], Res).

mk_vcs_main(Res) :-
	mk_vcs_vars([prime], VcsVars),
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
        %% done left&right old&new set to zero
        mk_done_var([left],         DoneL),
        mk_done_var([right],        DoneR),
        mk_done_var([left, prime],  DoneL1),
        mk_done_var([right, prime], DoneR1),
        
        format_atom('~p = 0, ~p = 0', [DoneL, DoneL1], Line1),
        format_atom('~p = 0, ~p = 0', [DoneR, DoneR1], Line2),

        findall(R, ir:register(R), Regs),
        findall(L, ir:link(L,_), UFs),

        %% issue a new taint bit
        %% new tags of source registers are set to 1
        findall(SO, ir:taint_source(SO), Sources),
        (   foreach(S, Sources),
            foreach(R1, Line3),
            param(Line3)
        do  mk_var_name([left,  tag, prime], S, SVLT1),
            mk_var_name([right, tag, prime], S, SVRT1),
            format_atom('~p=1,~p=1', [SVLT1, SVRT1], R1)
        ),
        mk_and(Line3,Line3And),

        %% reset other taint bits
        %% new tags of other registers are set to 0
        exclude(contains(Sources), Regs, ResetRegs),
        (   foreach(RR, ResetRegs),
            foreach(R2, Line4),
            param(Line3)
        do  mk_var_name([left,  tag, prime], RR, RRVLT1),
            mk_var_name([right, tag, prime], RR, RRVRT1),
            format_atom('~p=0,~p=0', [RRVLT1, RRVRT1], R2)
        ),
        mk_and(Line4,Line4And),
        
        %% all variable valuations stay the same.
        append(Regs,UFs,AllAtoms),
        (   foreach(A, AllAtoms),
            foreach(A2, Line5)
        do  mk_var_name([left],  A, AL_Old),
            mk_var_name([right], A, AR_Old),
            mk_var_name([left,  prime], A, AL_New),
            mk_var_name([right, prime], A, AR_New),
            format_atom('~p=~p,~p=~p', [AL_New, AL_Old, AR_New, AR_Old], A2)
        ),
        mk_and(Line5,Line5And),
        
        format_atom('~p,~n~p,~n~p,~n~p,~n~p',
                    [Line1,Line2,Line3And,Line4And,Line5And],
                    Res).

%% both not done: both executions take a step.
mk_vcs_main_next_step(Res) :-
        mk_next_vars([left],NextVarsLeft),
        mk_and(NextVarsLeft, NextVarsLeftAnd),

        mk_next_vars([right],NextVarsRight),
        mk_and(NextVarsRight, NextVarsRightAnd),

        findall(C, ir:cond_atom(C), CondAtoms),
        (   foreach(CA, CondAtoms),
            foreach(CE, CES),
            param(CES)
        do  mk_var_name([left],  CA, CVL),
            mk_var_name([right], CA, CVR),
            format_atom('~p = ~p', [CVL,CVR], CE)
        ),
        mk_and(CES,CondEqualities),

        %% both read same instructions
        query_ir(taint_source, Sources),
        (   foreach(SAtom, Sources),
            foreach(SI, SIS),
            param(SIS)
        do  mk_var_name([left,  prime],      SAtom, SVarL1),
            mk_var_name([right, prime],      SAtom, SVarR1),
            mk_var_name([tag, left,  prime], SAtom, STVarL1),
            mk_var_name([tag, right, prime], SAtom, STVarR1),
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
        mk_done_var([left],  DoneL),
        mk_done_var([right], DoneR),
        mk_vcs_vars(Vs),
        mk_and(Vs,VsAnd),
        format_atom('~p = 1 :-~ninv(~p), ~p = 1.', [DoneR,VsAnd, DoneL], Res).
        
mk_vc_sep(P,Res) :-
        format_atom('~n  ~p', [P], Res).
