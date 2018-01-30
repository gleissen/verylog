:- discontiguous small/1.

:- use_module('lib/misc.pl', [format_atom/3,
			      get_fresh_num/1,
			      mk_and/2,
			      mk_and/3]).

:- use_module('lib/utils.pl').

/*
==========================================
Clauses used in the intermediate language:
==========================================
register(R)
wire(W)
module_inst(ModuleName, InstName, InputArgs, OutputArgs)
always(Event, Statement)
taint_source(R)
taint_sink(R)
*/

query_ir(P, Ls) :-
        ( findall(F, current_predicate(P,F), Fs), length(Fs, N), N > 1 ->
            format('~p has multiple arities !', [P]), halt(1)
        ; IR = [ register
               , wire
               , link
               , always
               , taint_source
               , taint_sink
               ], \+ memberchk(P, IR) ->
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


/*
Creates Horn clause verification conditions from a intermediate language verilog file.
*/

mk_var_name(ID, VarName) :-
/* Transform an atom "ID" into variable name "V_ID". */	
	format_atom('V_~p',[ID], VarName).

%-- Transition relation.

mk_assignments(Res) :-
        query_ir(asn, Ls),
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

mk_next_def(Suffix, Res) :-
	mk_invariant_vars(Suffix, Vs),
	mk_and(Vs, Vs1),
	format_atom('~p1',[Suffix], PrimedSuffix),
	mk_invariant_vars(PrimedSuffix, VsPrimed),
	mk_and(VsPrimed, VsPrimed1),
	format_atom('next(~p, Done~p, ~p, Done~p1)',[Vs1,Suffix,VsPrimed1,Suffix], Res).

mk_sink_cond(Res) :-
	taint_sink(X)->
	mk_var_name(X, XV),
	format_atom('ite(~p1=1,Done1=1,Done1=Done)',[XV], Res).

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

mk_next(Res) :-
	mk_assignments(Asn),
	mk_links(Links),
	% Links=[],
	mk_and(Asn, Asn1),
	mk_and(Links, Links1),
	mk_and(Asn1, Links1, Bd),
	mk_next_def('',Hd),
	mk_reset(Reset),
	mk_sink_cond(Sink),
	mk_unassigned(Un),
	format_atom('Done=1, T1=T, Done1=Done',[], Spin),
	format_atom('~p := ~n(~n Done=0, ~p~n; Done=0, ~p, ~p,~p~n; ~p~n).',[Hd,Reset,Sink,Un,Bd,Spin], Res).

%-- Invariants.

mk_invariant_vars(Suffix, Vs1) :-
        query_ir(register,Vs),
	(   foreach(V, Vs),
	    foreach(V1, Vs1),
	    param(Suffix)
	do  mk_var_name(V, V0),
	    format_atom('~p~p', [V0,Suffix], V1)
	).

mk_invariant(Suffix, Res) :-
	mk_invariant_vars(Suffix, Vs1),
	mk_and(Vs1, Vs2),  
	format_atom('inv(~p, Done~p)', [Vs2, Suffix], Res).

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


%-- Initial states and property.

mk_init(Res) :-
	mk_invariant_vars('L=0', DefsL),
	mk_invariant_vars('R=0', DefsR),
	mk_and(DefsL, DefsL1),
	mk_and(DefsR, DefsR1),
	format_atom('~p,DoneL = 0, ~p, DoneR=0.',[DefsL1,DefsR1], Res).

mk_property(Res) :-
	mk_relational_invariant(Inv),
	format_atom('DoneR=1 :- ~p, DoneL=1.', [Inv], Res).

mk_query_naming(Res) :-
        query_ir(register,Vs),
	mk_and(Vs, Vs1),
	format_atom('query_naming(inv(~p, done, t)).', [Vs1], Res).

mk_vcs(Res) :-
	mk_init(Init),
	mk_relational_invariant(Inv),
	mk_primed_relational_invariant(Inv1),
	mk_next_def('L', NextL),
	mk_next_def('R', NextR),
	mk_property(Prop),
	format_atom('~p:-~p~n~p :- ~p,~n~p,~n~p.~n~p~n',[Inv,Init,Inv1,NextL,NextR,Inv,Prop], Res).

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
	
% flush_db :-
%         DynamicPredicates=[],
%         % ir_dynamic_predicates(DynamicPredicates),
%         (  foreach(D, DynamicPredicates)
%         % do abolish(D, [force(true)])
%         do retractall(D)
%         ). 

my_consult(File) :-
        % flush_db,
        consult(File),
        (current_predicate(parse_failed/1) -> halt(1); true),
        true.

main :-
        prolog_flag(argv, [Input|_]),
        % print_file(Input),
        my_consult(Input),
	mk_output_file(Res),
	format('~p',[Res]),
        true.

user:runtime_entry(start) :-
        main.
