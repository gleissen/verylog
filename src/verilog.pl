:- use_module('lib/misc.pl', [
			      format_atom/3,
			      get_fresh_num/1,
			      mk_and/2,
			      mk_and/3
			     ]).
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
	    format_atom("ite(~p=1, ~p1=1, ~p1=0)",[XV,YV,YV], Rel)
	).

mk_links(Res) :-
	findall(X-Y-Z, link(X,Y,Z), Ls),
	(   foreach(X-Y-Z, Ls),
	    foreach(Rel, Res)
	do  mk_var_name(X, XV),
	    mk_var_name(Y, YV),
	    mk_var_name(Z, ZV),
	    format_atom("ite((~p=1; ~p=1), ~p1=1, ~p1=0)",[XV,YV,ZV,ZV], Rel)
	).

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

mk_init(Res) :-
	findall(X, register(X), Vs),
	(   foreach(V, Vs),
	    fromto('', In, Out, Defs)
	do  mk_var_name(V, VN),
	    (   source(V)->
		format_atom('~p ~p1=1, ',[In,VN], Out)
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
	mk_init(Init),
	format_atom('Done=1, T1=T, Done1=Done',[], Spin),
	format_atom('~p:=~n(~n Done=0, ~p~n; Done=0, T1=T+1, ~p~n; ~p~n).',[Hd,Init,Bd,Spin], Res).

test :-
	consult(['../examples/minimal']),
	mk_next(Res),
	format('~p',[Res]).