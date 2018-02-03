:- module(ir, [
               read_ir/0,
               read_ir/1,
               query_ir/2,
               ir_stmt/1,
               ir_toplevel_list/1,
               done_var/1,
               done_atom/1,
               get_reg_vars/1,
               get_tag_vars/1,
               get_other_vars/1,
               get_all_vars/1,
               save/1,
               mk_vcs_vars/1,
               mk_next_vars/1,
               mk_next_vars/2,
               is_uf/1
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

:- dynamic cond_vars/1, ite/4.

wipe_db :-
        retractall(register(_)),
        retractall(wire(_)),
        retractall(module_inst(_,_,_)),
        retractall(always(_,_)),
        retractall(link(_,_)),
        retractall(asn(_,_)),
        retractall(taint_sink(_)),
        retractall(taint_source(_)),

        retractall(cond_vars(_)),
        retractall(ite(_,_,_,_)),

        true.

:- wipe_db.

save(X) :-
        assert(X).

ir_stmt([
         block,
         b_asn,
         nb_asn,
         ite
        ]).

ir_toplevel_list([
                  register, wire,
                  module_inst, always,
                  link, asn,
                  taint_source, taint_sink
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

done_var('Done').
done_atom('done').

read_ir(File) :-
        wipe_db,
        consult(File).

read_ir :-
        test_file(F),
        read_ir(F).


get_reg_vars(VsRegVars) :-
        query_ir(register,VsRegs),
        maplist(mk_var_name,VsRegs,VsRegVars).

get_tag_vars(VsTagVars) :-
        query_ir(register,VsRegs),
        maplist(mk_tagvar_name,VsRegs,VsTagVars).

get_other_vars([Done|UFVars]) :-
        done_var(Done),
        findall(X, link(X,_), UFAtoms),
        maplist(mk_var_name, UFAtoms, UFVars).

get_all_vars(VsAllVars) :-
        get_reg_vars(VsRegVars),
        get_tag_vars(VsTagVars),
        get_other_vars(VsOtherVars),
        flatten([VsRegVars,VsTagVars,VsOtherVars], VsAllVars).

test_file('$HOME/work/verilog/iverilog-parser/benchmarks/472-mips-pipelined/.472-mips-fragment.pl').


mk_vcs_vars(Vs) :-
        get_all_vars(AllVars),
        maplist(mk_lhs_name, AllVars, LeftVars),
        maplist(mk_rhs_name, AllVars, RightVars),
        append(LeftVars,RightVars,Vs).

mk_next_vars(Vs) :-
        get_all_vars(Vars),
        mk_next_vars(Vars,Vs).

mk_next_vars(Vars,Vs) :-
        maplist(mk_primed, Vars, Vars1),
        append(Vars,Vars1,Vs).
        
is_uf(Atom) :-
        atom(Atom), link(Atom, _).
