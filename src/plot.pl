:- use_module(library(lists)).
:- use_module('lib/misc.pl').
:- use_module('lib/ir.pl').

main :-
        prolog_flag(argv, [Input|_]),
        read_ir(Input),
        plot_assignments.

plot_assignments :-
        format('digraph {~n', []),

        findall(S, ir:always(_,S), AlwaysBlocks),
        (   foreach(Stmt, AlwaysBlocks)
        do  Stmt =.. [Name|Args],
            plot_stmt(Name,Args)
        ),

        findall(L-R, ir:asn(L,R), ContAsns),
        (   foreach(Lhs-Rhs, ContAsns)
        do  plot_assign([color(green)], Lhs,Rhs)
        ),

        findall(M-I-O, ir:module_inst(M,I,O), UFs),
        (   foreach(_-Inputs-Outputs, UFs)
        do  (   foreach(In, Inputs),
                param(Outputs)
            do  (   foreach(Out, Outputs),
                    param(In)
                do  plot_assign([color(orange)], Out, In)
                )
            )
        ),

        format('register [shape=ellipse];~n', []),
        format('wire     [shape=box];~n', []),
        format('register -> wire [color=orange, label="module", fontcolor=orange];~n', []),
        format('register -> wire [color=blue, label="uf", fontcolor=blue];~n', []),
        format('register -> wire [color=green, label="cont", fontcolor=green];~n', []),
        format('register -> wire [label="blocking", color=red, fontcolor=red];~n', []),
        format('register -> wire [color=black, label="non-blocking"];~n', []),

        format('}~n', []),

        true.

plot_link(F,Args) :-
        (   foreach(A, Args),
            param(F)
        do  plot_assign([color(green)], F, A)
        ).
        

plot_assign(Options, L, R) :-
        (   is_uf(R)   ->
            ir:link(R, Args),
            (   foreach(A, Args),
                param(L), param(Options)
            do  plot_assign([label(uf),fontcolor(blue)|Options], L, A)
            )
        ;   atom(R)    ->
            plot_node(L),
            plot_node(R),
            parse_options(Options, OptionsText),
            format('~p -> ~p [~p];~n',[R,L,OptionsText])
        ;   otherwise  ->
            throwerr('L <- R : weird rhs!')
        ).

parse_options([],'')       :- !.
parse_options(Options,Res) :-
        maplist(parse_option, Options, OptionsRes),
        mk_and(OptionsRes, Res).

parse_option(Option, Res) :-
        Option =.. [Name, Val],
        format_atom('~p="~p"', [Name, Val], Res).

plot_stmt(ite, [_, Then, Else]) :-
        !, 
        (   compound(Then) ->
            Then =.. [NameT|ArgsT],
            plot_stmt(NameT,ArgsT)
        ;   true
        ),
        (   compound(Else) ->
            Else =.. [NameE|ArgsE],
            plot_stmt(NameE,ArgsE)
        ;   true
        ).

plot_stmt(nb_asn,[L,R]) :- !,
        plot_assign([color(black)], L,R).

plot_stmt(b_asn,[L,R]) :- !,
        plot_assign([color(red)], L,R).

plot_stmt(block,[Stmts]) :- !,
        (   foreach(S,Stmts)
        do  S =.. [Name|Args],
            plot_stmt(Name,Args)
        ).

plot_stmt(Name,_) :- !,
        throwerr('plot stmt is not implemented for ~p', [Name]).

plot_node(N) :-
        (   ir:wire(N) ->
            format('~p [shape=box];~n', [N])
        ;   ir:register(N) ->
            format('~p [shape=ellipse];~n', [N])
        ;   is_uf(N) ->
            throwerr('node cannot be a UF!', [])
        ).
            
