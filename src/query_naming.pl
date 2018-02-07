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
        mk_vcs_vars([atom], VsAtoms),
        mk_and(VsAtoms,And),
        format_atom('query_naming(inv(~p)).', [And], Res).

