%% #############################################################################
%% ### OLD CODE ################################################################
%% #############################################################################

mk_assignments(Res) :-
        query_ir(nb_asn, Ls),
        (   foreach(X-Y, Ls),
            foreach(Rel, Res)
        do  mk_var_name(X, XV),
            mk_var_name(Y, YV),
            assert(assigned(Y)),
            format_atom("~p=~p1",[XV,YV], Rel)
        ).

mk_links(Res) :-
        query_ir(link, Ls),
	(   foreach(X-Y-Z, Ls),
	    foreach(Rel, Res)
	do  mk_var_name(X, XV),
	    mk_var_name(Y, YV),
	    mk_var_name(Z, ZV),
	    assert(assigned(Z)),
	    format_atom("ite((~p=1; ~p=1), ~p1=1, ~p1=0)",[XV,YV,ZV,ZV], Rel)
	).

mk_unassigned(Res) :-
	findall(X, (query_ir(register,Rs), memberchk(X, Rs), \+assigned(X)), Vs),
	(   foreach(V, Vs),
	    foreach(Def, Defs)
	do  mk_var_name(V, VN),
	    format_atom('~p1=0',[VN], Def)
	),
	mk_and(Defs, Res).

mk_reset(Res) :-
        query_ir(register,Vs),
	(   foreach(V, Vs),
	    fromto('', In, Out, Defs)
	do  mk_var_name(V, VN),
	    (   taint_source(V)->
		format_atom('~p (~p1=1;~p1=0), ',[In,VN,VN], Out)
	    ;   format_atom('~p ~p1=0, ',[In,VN], Out)
	    )
	),
	format_atom('~p Done1=0', [Defs], Res).

mk_init(Res) :-
	mk_invariant_vars('L=0', DefsL),
	mk_invariant_vars('R=0', DefsR),
	mk_and(DefsL, DefsL1),
	mk_and(DefsR, DefsR1),
	format_atom('~p,DoneL = 0, ~p, DoneR=0.',[DefsL1,DefsR1], Res).

mk_property(Res) :-
	mk_relational_invariant(Inv),
	format_atom('DoneR=1 :- ~p, DoneL=1.', [Inv], Res).


mk_vcs(Res) :-
	mk_init(Init),
	mk_relational_invariant(Inv),
	mk_primed_relational_invariant(Inv1),
	mk_next_def('L', NextL),
	mk_next_def('R', NextR),
	mk_property(Prop),
	format_atom('~p:-~p~n~p :- ~p,~n~p,~n~p.~n~p~n',[Inv,Init,Inv1,NextL,NextR,Inv,Prop], Res).


mk_invariant(Suffix, Res) :-
	mk_invariant_vars(Suffix, Vs1),
	mk_and(Vs1, Vs2),  
	format_atom('inv(~p, Done~p, T~p)', [Vs2, Suffix, Suffix], Res).

mk_invariant(Res) :-
	mk_invariant('', Res).

mk_primed_invariant(Res) :-
	mk_invariant('1', Res).

mk_relational_invariant(Res) :-
	mk_relational_invariant('',Res).

mk_primed_relational_invariant(Res) :-
	mk_relational_invariant('1', Res).

mk_relational_invariant(Suffix, Res) :-
	format_atom('L~p', [Suffix], SuffixL),
	format_atom('R~p', [Suffix], SuffixR),
	mk_invariant_vars(SuffixL, VLs),
	mk_invariant_vars(SuffixR, VRs),
	format_atom('DoneL~p', [Suffix], DoneL),
	format_atom('DoneR~p', [Suffix], DoneR),
	append([DoneR|VRs], [DoneL|VLs], V1s),
	mk_and(V1s, Vs2),  
	format_atom('inv(~p)', [Vs2], Res).
