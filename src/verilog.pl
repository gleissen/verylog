:- use_module('lib/misc.pl', [
			      format_atom/3,
			      get_fresh_num/1,
			      mk_and/2,
			      mk_and/3
			     ]).

:- dynamic assigned/1.
/*
Creates Horn clause verification conditions from a intermediate language verilog file.
*/

mk_var_name(ID, VarName) :-
/* Transform an atom "ID" into variable name "V_ID". */	
	format_atom('V_~p',[ID], VarName).

mk_assignments(Res) :-
	findall(X-Y, asn(X,Y), Ls),
	(   foreach(X-Y, Ls),
	    foreach(Rel, Res)
	do  mk_var_name(X, XV),
	    mk_var_name(Y, YV),
	    assert(assigned(Y)),
	    format_atom("ite(~p=1, ~p1=1, ~p1=0)",[XV,YV,YV], Rel)
	).

mk_links(Res) :-
	findall(X-Y-Z, link(X,Y,Z), Ls),
	(   foreach(X-Y-Z, Ls),
	    foreach(Rel, Res)
	do  mk_var_name(X, XV),
	    mk_var_name(Y, YV),
	    mk_var_name(Z, ZV),
	    assert(assigned(Z)),
	    format_atom("ite((~p=1; ~p=1), ~p1=1, ~p1=0)",[XV,YV,ZV,ZV], Rel)
	).

mk_unassigned(Res) :-
	findall(X, (register(X),\+assigned(X)), Vs),
	(   foreach(V, Vs),
	    foreach(Def, Defs)
	do  mk_var_name(V, VN),
	    format_atom('~p1=0',[VN], Def)
	),
	mk_and(Defs, Res).

mk_next_def(Res) :-
	findall(X, register(X), [V0|Vs]),
	mk_var_name(V0, V0N),
	format_atom('next(~p',[V0N],S0),
	format_atom('~p1', [V0N], S0p),
	(   foreach(V, Vs),
	    fromto(S0, In, Out, S),
	    fromto(S0p, Inp, Outp, Sp)
	do  mk_var_name(V, VN),
	    format_atom("~p, ~p",[In,VN], Out),
	    format_atom('~p, ~p1', [Inp,VN], Outp)
	),
	format_atom('~p, Done, T, ~p, Done1, T1)',[S,Sp], Res).

mk_sink_cond(Res) :-
	sink(X)->
	mk_var_name(X, XV),
	format_atom('ite(~p1=1,Done1=1,Done1=Done)',[XV], Res).

mk_reset(Res) :-
	findall(X, register(X), Vs),
	(   foreach(V, Vs),
	    fromto('', In, Out, Defs)
	do  mk_var_name(V, VN),
	    (   source(V)->
		format_atom('~p (~p1=1;~p1=0), ',[In,VN,VN], Out)
	    ;   format_atom('~p ~p1=0, ',[In,VN], Out)
	    )
	),
	format_atom('~p Done1=0, T1=0', [Defs], Res).

mk_next(Res) :-
	mk_assignments(Asn),
	mk_links(Links),
	mk_and(Asn, Asn1),
	mk_and(Links, Links1),
	mk_and(Asn1, Links1, Bd),
	mk_next_def(Hd),
	mk_reset(Reset),
	mk_sink_cond(Sink),
	mk_unassigned(Un),
	format_atom('Done=1, T1=T, Done1=Done',[], Spin),
	format_atom('~p:=~n(~n Done=0, ~p~n; Done=0, T1=T+1, ~p, ~p,~p~n; ~p~n).',[Hd,Reset,Sink,Un,Bd,Spin], Res).

mk_invariant(Res) :-
	mk_invariant(Res, '').

mk_primed_invariant(Res) :-
	mk_invariant(Res, '1').

mk_invariant(Res, Suffix) :-
	findall(X, register(X), Vs),
	(   foreach(V, Vs),
	    foreach(V1, Vs1),
	    param(Suffix)
	do  mk_var_name(V, V0),
	    format_atom('~p~p', [V0,Suffix], V1)
	),
	mk_and(Vs1, Vs2),  
	format_atom('inv(~p, Done~p, T~p)', [Vs2, Suffix, Suffix], Res).

mk_init(Res) :-
	findall(X, register(X), Vs),
	(   foreach(V, Vs),
	    foreach(Def, Defs)
	do  mk_var_name(V, V0),
	    format_atom('~p=0', [V0], Def)
	),
	mk_and(Defs, Defs1),
	format_atom('~p, Done=0, T=0.',[Defs1], Res).

mk_property(Res) :-
	mk_invariant(InvL, 'L'),
	mk_invariant(InvR, 'R'),
	format_atom('TL=TR :- ~p,~p, DoneL=1, DoneR=1.', [InvL, InvR], Res).

mk_query_naming(Res) :-
	findall(X, register(X), Vs),
	mk_and(Vs, Vs1),
	format_atom('query_naming(inv(~p, done, t)).', [Vs1], Res).
mk_vcs(Res) :-
	mk_init(Init),
	mk_invariant(Inv),
	mk_primed_invariant(Inv1),
	mk_next_def(Next),
	mk_property(Prop),
	format_atom('~p:-~p~n~p :- ~p,~n~p.~n~p~n',[Inv,Init,Inv1,Next,Inv,Prop], Res).

cleanup :-
	retractall(assigned).

mk_output_file(Res) :-
	mk_query_naming(Naming),
	mk_next(Next),
	mk_vcs(Vcs),
	format_atom('~p~n~p~n~p~n',[Naming,Next,Vcs], Res).
	
test :-
	consult(['../examples/minimal']),
	cleanup,
	mk_output_file(Res),
	format('~p',[Res]).