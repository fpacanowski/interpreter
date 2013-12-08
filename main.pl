:- use_module(interpreter).

input(load) --> ":l ".
input(eval) --> ":e ".
input(quit) --> ":q".
input(quit) --> [end_of_file].

process(load, Filename) :-
	read_file(Filename, F),
	interp(F).

process(eval, Expr) :-
	eval(Expr, Res),
	writeln(Res).

main :-
	write('> '),
	read_line_to_codes(user_input, Line),
	input(Cmd, Line, Param),
	writeln(Cmd),
	process(Cmd, Param),
	(
		var(Cmd),fail;
		Cmd \= quit
	),
	main.

test(X) :-
	interp("foo = 7;"),
	eval("foo", X).

%%%inspired by http://boklm.eu/prolog/page_9.html#932

treatfile(T) :- current_input(Stream), read_line_to_codes(Stream, Term), treat(Term, T).

treat( end_of_file, []) :- !.
treat(Term, [Term1|T]) :- append(Term, "\n", Term1), treatfile(T).

read_file(Filename, F) :-
	atom_codes(FilenameAtom, Filename),
	see(FilenameAtom),
	treatfile(FF),
	flatten(FF, F),
	%atom_codes(F, FFF),
	seen.
