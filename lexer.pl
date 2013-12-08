:- module(lexer, [lexer/3]).

whatever --> [].
whatever --> [_], whatever.
whitespace --> [X], {code_type(X, space)},!, whitespace.
whitespace --> [].

comment --> "--", whatever, "\n".

lexer(Tokens) -->
	whitespace,
	(
		comment, lexer(Tokens);
		token(Token),!,{ Tokens = [Token | TokList] },lexer(TokList);
		[],{ Tokens = [] }
	), !.

token(tkWhere)   --> "where", !.
token(tkLTE)     --> "<=".
token(tkGTE)     --> ">=".
token(tkLT)      --> "<".
token(tkGT)      --> ">".
token(tkNE)      --> "/=".
token(tkEq)      --> "=".
token(tkLambda)  --> "\\".
token(tkArrow)   --> "->".
token(tkPlus)    --> "+".
token(tkMinus)   --> "-".
token(tkTimes)   --> "*".
token(tkDiv)     --> "div".
token(tkMod)     --> "mod".
token(tkSc)      --> ";".
token(tkLPar)    --> "(".
token(tkRPar)    --> ")".
token(tkLBra)    --> "{".
token(tkRBra)    --> "}".

token(tkId(IdAtom)) --> identifier(IdAtom).
token(tkNr(Nr)) --> digit(X), number(X, Nr).

%following predicates are inspired by TWi lexer
letter(L) -->
	[L], { code_type(L, alpha) }.

alphanum([A|T]) -->
	[A], { code_type(A, alnum) }, !, alphanum(T).
alphanum([]) -->
	[].

identifier(Id) -->
	letter(L),
	alphanum(As),
	{ atom_codes(Id, [L|As]) }.

digit(D) -->
	[D],
	{ code_type(D, digit) }.

digits([D|T]) -->
	digit(D),
	!,
	digits(T).
digits([]) -->
	[].

number(D, Nr) -->
	digits(Ds),
	{ number_chars(Nr, [D|Ds]) }.

:- begin_tests(lexer).

test(whitespace) :-
        whitespace(" ", []),
        whitespace("  ", []),
        whitespace([9], []),
	\+whitespace("x", []).

test(comment) :-
	lexer([tkId(foo), tkEq, tkNr(7), tkSc], "-- fafdldak-r-r32-e--3r2-\n  foo = 7;", []).

test(lexing) :-
	lexer([tkLT, tkLT, tkLT, tkLT, tkLT], "<   < < < <", []),
	lexer([tkLT, tkLT, tkLT, tkLT, tkLT], "<   < < < <  ", []),
	lexer([tkLT, tkLTE, tkId(foo), tkNr(123)], "< <=   foo 123", []).

test(maximal_munch) :-
	lexer([tkLTE], "<=", []),
	lexer([tkLT, tkEq], "< =", []),
	lexer([tkGTE], ">=", []),
	lexer([tkGT, tkEq], "> =", []).

test(identifier) :-
	identifier(foo, "foo", []),
	lexer([tkId(foo)], "foo", []).

:- end_tests(lexer).
