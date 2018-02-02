:- module(query_naming, [mk_query_naming/1], [hidden(true)]).

:- use_module(library(lists)).

:- use_module('lib/ir.pl').
:- use_module('lib/misc.pl').

%% #############################################################################
%% ### INITIAL STATES AND PROPERTY #############################################
%% #############################################################################

%% prints the query_naming predicated required by qarmc
%% i.e. query_naming(inv(...)).
mk_query_naming(Res) :-
        mk_vcs_vars(Vs),
        maplist(mk_atom_name, Vs, _VsAtoms),
        (   foreach(V, _VsAtoms),
            foreach(V1, VsAtoms),
            param(VsAtoms)
        do  (   atom_chars(V, ['v', '_', 'V', '_', 'v', '_'|_]) ->
                sub_atom(V,4,_,0,V1)
            ;   V1 = V
            )
        ),
        mk_and(VsAtoms,And),
        format_atom('query_naming(inv(~p)).', [And], Res).

