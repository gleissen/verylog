:- module(utils, [ print_file/1
                 ], [hidden(true)]).

print_file(File) :-
        open(File, read, Stream),
        print_file_helper(Stream),
        close(Stream) .

print_file_helper(Stream) :-
        read(Stream, X),
        ( \+ at_end_of_stream(Stream) ->
            (format('~p~N', [X]), print_file_helper(Stream))
        ; true
        ).