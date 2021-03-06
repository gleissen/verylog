/*
Creates Horn clause verification conditions from a intermediate language verilog file.
*/

:- module(verylog, [main/0], [hidden(true)]).

:- use_module(library(lists)).
:- use_module(library(file_systems)).

:- use_module('lib/misc.pl').
:- use_module('lib/ir.pl').

:- use_module('initial_pass.pl').
:- use_module('query_naming.pl').
:- use_module('transition.pl').
:- use_module('vcgen.pl').

mk_output_file(Res) :-
        Print_query_naming = true,
        Print_trans_rel    = true,
        Print_vcs          = true,
        
        (   Print_query_naming -> 
            mk_query_naming(QNaming)
        ;   QNaming = ''
        ),

        (   Print_trans_rel ->
            mk_next(Next)
        ;   Next = ''
        ),

        (   Print_vcs ->
            mk_vcs(Vcs)
        ;   Vcs = ''
        ),

        mk_header(Header),

        format_atom('~p~n~n~p~n~n~p~n~n~p', [Header, QNaming, Next, Vcs], Res),
        true.
	
main :-
        prolog_flag(argv, [Input|_]),
        read_ir(Input),
        run_initial_pass,
	mk_output_file(Res),
	format('~p',[Res]),
        true.
        

mk_header(Header) :-
        inline_comment('-*- mode: prolog -*-', Line1),
        inline_comment('vim: set ft=prolog:', Line2),
        format_atom('~p~n~p~n', [Line1, Line2], Header).
