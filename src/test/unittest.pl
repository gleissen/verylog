:- use_module(library(lists)).
:- use_module(library(file_systems)).

:- use_module('../lib/misc.pl').
:- use_module('../lib/ir.pl').

:- use_module('../initial_run.pl').
:- use_module('../query_naming.pl').
:- use_module('../transition.pl').
:- use_module('../vcgen.pl').

:- use_module(library(plunit)).

:- begin_tests(verylog).

runner(_F, In, _Out) :-
        consult_list(In),
        true.

test(dummy) :-
        F    = tr_body,
        In   = [ register(x)
               , register(y)
               , always( event1(star)
                       , nb_asn(x, y)
                       )
               ],
        Out  = [],
        runner(F, In, Out).

test(dummy) :-
        fail.

:- end_tests(verylog).

unit_test :-
        set_prolog_flag(informational, on),
        run_tests(verylog, [verbose]).
