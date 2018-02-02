/*
Creates Horn clause verification conditions from a intermediate language verilog file.
*/

:- use_module(library(lists)).
:- use_module(library(file_systems)).

:- use_module('lib/misc.pl').
:- use_module('lib/ir.pl').

:- use_module('initial_run.pl').
:- use_module('query_naming.pl').
:- use_module('transition.pl').
:- use_module('vcgen.pl').

mk_output_file(Res) :-
	mk_query_naming(Naming),
        format_atom('~p', [Naming], Res0),

	mk_next(Next),
        format_atom('~p', [Next], Res1),

	mk_vcs(Vcs),
        format_atom('~p', [Vcs], Res2),

        format_atom('~n~n~p~n~n~p~n~n~p', [Res0, Res1, Res2], Res),
        true.
	
main :-
        prolog_flag(argv, [Input|_]),
        read_ir(Input),
        runInput.

runInput :-
        run_initial_pass,
	mk_output_file(Res),
	format('~p',[Res]).
        
user:runtime_entry(start) :-
        main.

test :- read_ir, runInput.

