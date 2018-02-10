:- module(ir, [
               consult_list/1,
               get_all_vars/2,
               ir_stmt/1,
               ir_toplevel_list/1,
               is_uf/1,
               done_atom/1,
               mk_done_var/2,
               mk_next_vars/1,
               mk_next_vars/2,
               mk_var_name/2,
               mk_var_name/3,
               mk_vcs_vars/1,
               mk_vcs_vars/2,
               query_ir/2,
               read_ir/0,
               read_ir/1,
               save/1
              ], [hidden(true)]).

:- use_module(library(lists)).
:- use_module('misc.pl').

/*
==========================================
Clauses used in the intermediate language:
==========================================
register(R)
wire(W)
module_inst(ModuleName, Inputs, Outputs)
always(Event, Statement)
taint_source(R)
taint_sink(R)
ite(Cond,Then,Else)
asn(Lhs,Rhs)     // assign L = R
b_asn(Lhs,Rhs)   // L = R
nb_asn(Lhs,Rhs)  // L <= R
link(OutputName, InputVars)
*/

:- multifile register/1, wire/1, module_inst/3, always/2, link/2, asn/2, taint_source/1, taint_sink/1.
:- dynamic   register/1, wire/1, module_inst/3, always/2, link/2, asn/2, taint_source/1, taint_sink/1.

:- dynamic cond_atom/1, ite/4.

wipe_db :-
        retractall(register(_)),
        retractall(wire(_)),
        retractall(module_inst(_,_,_)),
        retractall(always(_,_)),
        retractall(link(_,_)),
        retractall(asn(_,_)),
        retractall(taint_sink(_)),
        retractall(taint_source(_)),

        retractall(cond_atom(_)),

        true.

:- wipe_db.

save(X) :-
        assert(X).

ir_stmt([ block
        , b_asn
        , nb_asn
        , ite
        , skip
        ]).

ir_toplevel_list([ register
                 , wire
                 , always
                 , link
                 , asn
                 , taint_source
                 , taint_sink
                 ]).
        
query_ir(P, Ls) :-
        ( findall(F, current_predicate(P,F), [_,_|_]) ->
            throwerr('~p has multiple arities !', [P])
        ; ir_toplevel_list(IR), \+ memberchk(P, IR) ->
            throwerr('~p does not belong to the IR !', [P])
        ; true
        ),                      % sanity check
        ( current_predicate(P,F), functor(F,N,A)  ->
            ( A = 1 -> findall(X,     call(N,X),     Ls)
            ; A = 2 -> findall(X-Y,   call(N,X,Y),   Ls)
            ; A = 3 -> findall(X-Y-Z, call(N,X,Y,Z), Ls)
            ; throwerr('Unknown predicate in query: ~p~n', [P])
            )
        ; Ls=[]
        ).

read_ir(File) :-
        wipe_db,
        consult(File).

read_ir :-
        test_file(F),
        read_ir(F).


get_reg_vars(Options, VsRegVars) :-
        query_ir(register,VsRegs),
        maplist(mk_var_name(Options),VsRegs,VsRegVars).

get_tag_vars(Options, VsTagVars) :-
        query_ir(register,VsRegs),
        maplist(mk_var_name([tag|Options]),VsRegs,VsTagVars).

get_other_vars(Options, OtherVars) :-
        done_atom(DoneAtom),
        findall(X, link(X,_), UFAtoms),
        maplist(mk_var_name(Options), [DoneAtom|UFAtoms], OtherVars).

get_all_vars(Options, VsAllVars) :-
        get_reg_vars(Options, VsRegVars),
        get_tag_vars(Options, VsTagVars),
        get_other_vars(Options, VsOtherVars),
        flatten([VsRegVars,VsTagVars,VsOtherVars], VsAllVars).

get_all_vars(AllVars) :- get_all_vars([], AllVars).

test_file('$HOME/work/verilog/iverilog-parser/benchmarks/472-mips-pipelined/.472-mips-fragment.pl').

mk_vcs_vars(Vs) :-
        mk_vcs_vars([], Vs).

mk_vcs_vars(Options, Vs) :-
        get_all_vars([left|Options],  LeftVars),
        get_all_vars([right|Options], RightVars),
        append(LeftVars, RightVars, Vs).

mk_next_vars(Vs) :- mk_next_vars([], Vs).

mk_next_vars(Options, Vs) :-
        get_all_vars(Options, Vars),
        get_all_vars([prime|Options], PrimedVars),
        append(Vars,PrimedVars,Vs).

is_uf(Atom) :-
        atom(Atom), link(Atom, _).

consult_list(ToplevelIRList) :-
        wipe_db,
        (   foreach(ToplevelIR, ToplevelIRList)
        do  assert(ToplevelIR)
        ).

%% VLT1_...

mk_var_name(ID, VarName) :-
        mk_var_name([], ID, VarName).

%% options are: left, right, tag, prime
mk_var_name(Options, ID, VarName) :-
        parse_options(Options, Suffix),
        add_prefix(Suffix, ID, VarName).

parse_options(Options, Suffix) :-
        (   memberchk(left, Options), memberchk(right, Options) ->
            throwerr('mk_var_name is given both left & right')
        ;   memberchk(left, Options) ->
            Pos = 'L'
        ;   memberchk(right, Options) ->
            Pos = 'R'
        ;   otherwise ->
            Pos = ''
        ),
        (   memberchk(tag, Options) ->
            Tag = 'T'
        ;   otherwise ->
            Tag = ''
        ),
        (   memberchk(prime, Options) ->
            Prime = '1'
        ;   otherwise ->
            Prime = ''
        ),
        (   memberchk(atom, Options) ->
            Atom = 'v'
        ;   otherwise ->
            Atom = ''
        ),
        format_atom('~pV~p~p~p_', [Atom, Pos, Tag, Prime], Suffix).

done_atom('done').

mk_done_var(Options, VarName) :-
        done_atom(DoneAtom),
        mk_var_name(Options, DoneAtom, VarName).
