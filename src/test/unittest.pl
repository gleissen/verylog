:- use_module(library(lists)).
:- use_module(library(file_systems)).

:- use_module('../lib/misc.pl').
:- use_module('../lib/ir.pl').

:- use_module('../initial_run.pl').
:- use_module('../query_naming.pl').
:- use_module('../transition.pl').
:- use_module('../vcgen.pl').

:- use_module(library(plunit)).


remove_single_line_comments([], []) :- !.
remove_single_line_comments([37|T], L) :-
        remove_until_nl(T,Rest),
        remove_single_line_comments(Rest, L).
remove_single_line_comments([H|T], L) :-
        remove_single_line_comments(T, L1),
        L = [H|L1].

remove_multi_line_comments([], []) :- !.
remove_multi_line_comments([47,42|T], L) :- !,
        remove_until_close_comment(T,Rest),
        remove_multi_line_comments(Rest, L).
remove_multi_line_comments([H|T], L) :-
        remove_multi_line_comments(T, L1),
        L = [H|L1].

remove_until_close_comment([42,47|T], T) :- !.
remove_until_close_comment([_|T], T1)    :- remove_until_close_comment(T,T1).

remove_until_nl([10|T], T)  :- !.
remove_until_nl([_|T],  T1) :- remove_until_nl(T, T1).

filter_whitespace_list([], [])   :- !.
filter_whitespace_list([H|T], L) :-
        filter_whitespace_list(T,L1),
        (   (H = 32 ; H = 10 ; H = 9) ->
            L = L1
        ;   otherwise ->
            L = [H|L1]
        ).

filter_whitespace_atom(Atom, Atom1) :-
        atom_codes(Atom, Codes),
        remove_single_line_comments(Codes, Codes1),
        remove_multi_line_comments(Codes1, Codes2),
        filter_whitespace_list(Codes2, Codes3),
        atom_codes(Atom1, Codes3).

%% +F   : functor name to call
%% +In  : list of toplevel IR elements
%% +Out : Output string
%% -Exp : Expected result atom
%% -Res : Result atom (i.e. F(Res))
runner(F, In, Out, Exp, Res) :-
        consult_list(In),
        run_initial_pass,
        call(F, _Res),
        filter_whitespace_atom(_Res, Res),
        atom_codes(OutAtom, Out),
        filter_whitespace_atom(OutAtom, Exp).

:- begin_tests(verylog).

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% BEGINNING OF UNIT TESTS
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test(tr_body, true(Res = Exp)) :-
        F    = mk_next_body,
        In   = [ register(x)
               , register(y)
               , taint_sink(y)
               , always( event1(star)
                       , nb_asn(y, x)
                       )
               ],
        Out = " \
        ( \
          true, \
          assign_op(V_y_t1, V_x_t, V_y1, V_x), \
          true, \
          ite(V_y_t1>=1, Done1=1, Done1 = Done), \
          Done = 0 \
        )",
        runner(F, In, Out, Exp, Res).

test(tr_body, true(Res = Exp)) :-
        F    = mk_next_body,
        In   = [ register(a)
               , register(b)
               , taint_sink(b)
               , always( event1(star)
                       , b_asn(b, a)
                       )
               ],
        Out = " \
        ( \
          true, \
          assign_op(V_b_t1, V_a_t, V_b1, V_a), \
          true, \
          ite(V_b_t1>=1, Done1=1, Done1 = Done), \
          Done = 0 \
        )",
        runner(F, In, Out, Exp, Res).

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% END OF UNIT TESTS
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- end_tests(verylog).

unit_test :-
        set_prolog_flag(informational, on),
        run_tests(verylog, [verbose]),
        set_prolog_flag(informational, off).
