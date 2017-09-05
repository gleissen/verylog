:- use_module('lib/misc.pl', [format_atom/3]).

mk_var_name(ID, VarName) :-
/* Transform an atom "ID" into variable name "V_ID". */	
	format_atom('V_~p',[ID], VarName).

mk_assignments(Res) :-
	findall(X-Y, asn(X,Y), Ls),
	(   foreach(X-Y, Ls),
	    foreach(Rel, Res)
	do  mk_var_name(X, XV),
	    mk_var_name(Y, YV),
	    format_atom("next(~p,~p1):=ite(~p=1, ~p1=1, ~p1=0).",[XV,YV,XV,YV,YV], Rel)
	).

test :-
	consult(['../examples/minimal']),
	mk_assignments(Res),
	format('~p',[Res]).