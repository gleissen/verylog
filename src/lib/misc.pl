/* This module contains various utility predicates */

:- module(misc, [
		 copy_instantiate/4,
		 format_atom/3,
		 fresh_pred_sym/1,
		 get_fresh_num/1,
		 get_ord_pairs/2,
		 get_pairs/2,
		 mk_and/2,
		 mk_and/3,
		 negate/2, bb_inc/1,
		 reset_fresh_num/0,
		 reset_pred_sym/0,
		 substitute_term/4,
		 substitute_term_avl/4,
                 add_prefix/3,
                 add_suffix/3,
                 contains/2,
                 dot/3,
                 droplist/3,
                 flatten/2,
                 flip/3,
                 fold/4,
                 inline_comment/2,
                 missing_atom/2,
                 mk_ite/4,
                 mk_nl/2,
                 mk_sum/2,
                 print_file/1,
                 throwerr/2,
                 warn/2
		], [hidden(true)]).
:- use_module(library(codesio)).
:- use_module(library(ordsets)).
:- use_module(library(terms)).
:- use_module(library(avl)).
:- use_module(library(lists)).

mk_and(L,R) :- rev(L, L1), mk_and_(L1, R).

mk_and_([], true).
mk_and_([H|T], R) :-
        foreach(X, T),
        fromto(H, In, Out, R)
        do
        mk_and(X, In, Out).

mk_and(true,  R,     R)     :- !.
mk_and(false, _,     false) :- !.
mk_and(R,     true,  R)     :- !.
mk_and(_,     false, false) :- !.
mk_and(A,     B,     (A, B)).

bb_inc(Key) :-
	bb_get(user:Key, I),
	I1 is I+1,
        bb_put(user:Key, I1).

/* Copy T and instantiate Q to V in the new term */
copy_instantiate(T, Q, V, T1) :-
	term_variables_set(T, TVars),
	term_variables_set(Q, QVars),
	ord_subtract(TVars, QVars, FVars),
	copy_term(T-FVars-Q, T1-FVars-V).

/* T1=T[X1/X] : T1 is the result of replacing each occurrence of X in T by X1. */
substitute_term(X1, X, T, T1) :-
	(   T==X ->
	    T1=X1
	;   compound(T) -> 
	    functor(T, Sym, Arity)->
	    functor(T1, Sym, Arity),
	    (   foreacharg(TI, T),
		foreacharg(T1I, T1),
		param([X,X1])
	    do  substitute_term(X1, X, TI, T1I)
	    )
	;   T1=T
	).

/* AVL1:=AVL[X1/X]. Rebuilds AVL since subtituting might result in an unbalanced tree. */
substitute_term_avl(X1, X, AVL, AVL1) :-
	avl_to_list(AVL, L),
	substitute_term(X1, X, L, L1),
	list_to_avl(L1, AVL1).

get_pairs([], []).
get_pairs([S|Set], Pairs) :-
	(   foreach(S1, Set),
	    foreach((S,S1), SPairs),
	    param(S)
	do  true
	),
	get_pairs(Set, RecPairs),
	append(SPairs, RecPairs, Pairs).

get_ord_pairs(Set, Pairs) :-
	ord_setproduct(Set, Set, Product),
	(   foreach(S, Set),
	    foreach(S-S, Diag)
	do  true
	),
	ord_subtract(Product, Diag, Pairs).

reset_fresh_num :-
	bb_put(fresh_num, 0).

get_fresh_num(N) :-
	(  bb_get(fresh_num, N) ->
	    true
	;  N=0
	),
	N1 is N+1,
	bb_put(fresh_num, N1).

reset_pred_sym :-
	bb_put(sym_num, 0).

fresh_pred_sym(Sym) :-
	(  bb_get(sym_num, N) ->
	    true
	;  N=0
	),
	N1 is N+1,
	bb_put(sym_num, N1),
	atom_codes(c, Prefix),
	number_codes(N, NumCodes),
	append(Prefix, NumCodes, Codes),
	atom_codes(Sym, Codes).

format_atom(Format, Arguments, Atom) :-
	format_to_codes(Format, Arguments, Codes),
	atom_codes(Atom, Codes).

/*LIA terms: negation */

% Negating A

negate(A=B, A\==B).
negate(A==B, A\==B).
negate(A\==B, A==B).
negate(A=\=B, A==B).

mk_sum([],_) :-
        format('empty list is given to mk_sum', []),
        halt(1).

mk_sum([H|T],Res) :-
        % rev(L, [H|T]),
        (   foreach(X, T),
            fromto(H, In, Out, Res)
        do  Out = In + X
        ).

flatten([], []).
flatten([H|T], L) :-
        is_list(H),
        flatten(T, L2),
        append(H, L2, L).

contains(List, Elem) :- memberchk(Elem, List).

warn(Format,Args) :-
        format(user_error, Format, Args),
        format(user_error, '~n', []).

print_file(File) :-
        open(File, read, Stream),
        print_file_helper(Stream),
        close(Stream) .

print_file_helper(Stream) :-
        read(Stream, X),
        ( \+ at_end_of_stream(Stream) ->
            (format('~p~n', [X]), print_file_helper(Stream))
        ; true
        ).

add_suffix(S,X,X1) :-
        format_atom('~p~p', [X,S], X1).

add_prefix(P,X,X1) :-
        format_atom('~p~p', [P,X], X1).

mk_nl(X,X1) :-
        format_atom('~p~n', [X], X1).

mk_ite(Cond,Then,Else,Res) :-
        format_atom('ite(~p, ~p, ~p)', [Cond, Then, Else], Res).

missing_atom(P, Res) :-
        inline_comment(P, Comment),
        format_atom('~p true', [Comment], Res).

inline_comment(P, Comment) :-
        atom_codes(CB, "/*"),
        atom_codes(CE, "*/"),
        format_atom('~p ~p ~p', [CB, P, CE], Comment).

dot([],In,In).
dot([H|T],In,Out) :-
        dot(T, In, _Out),
        call(H, _Out, Out).

fold(_,A,[],A) :- !.
fold(P,A,[H|T],R) :-
        !,
        call(P,A,H,A2),
        fold(P,A2,T,R).

fold(_,_,T,_) :-
        throwerr('~n!!! fold for ~p is not yet implemented !!!~n', [T]).

flip(A,F,R) :- call(F,A,R).


throwerr(Format,Args) :-
        warn(Format, Args),
        % true.
        false.
        % halt(1).
