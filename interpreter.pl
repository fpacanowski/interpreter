:- module(interpreter, [interp/1, eval/2]).
:- use_module(lexer).
:- use_module(parser).

trans(var(X), Y, Binding) :- Binding = (var(X),Y), !.
trans(X, Y, Bindings) :-
	X =.. [constr,ConsName|ConsArgs],
	trans(ConsArgs, TransConsArgs, Bindings),
	Y =.. [constr,ConsName|TransConsArgs].

trans([], [], []).
trans([H|T], [TH|TT], [B|Bindings]) :-
	trans(H, TH, B),
	trans(T, TT, Bindings).

applicate([], Acc, Acc).
applicate([H|T], Acc, Res) :-
	Acc1 =.. [app, Acc, H],
	applicate(T, Acc1, Res).

build_pattern_matcher([], [], true).
build_pattern_matcher([A|Arguments], [B|Pattern], (interpreter:red_to_constr(A,C),B=C,T)) :-
	nonvar(B),
	B =.. [constr|_],!,
	build_pattern_matcher(Arguments, Pattern, T).
build_pattern_matcher([A|Arguments], [B|Pattern], (A=B,T)) :-
	build_pattern_matcher(Arguments, Pattern, T).

translate_head(Head, TransHead, Bindings, PatternMatcher) :-
	Head =.. [clh, Function|Pattern],
	length(Pattern, NrOfArgs),
	length(Args, NrOfArgs),
	trans(Pattern, TransHeadList, Bindings1),
	build_pattern_matcher(Args, TransHeadList, PatternMatcher), 
	applicate(Args, Function, TransHead),
	flatten(Bindings1,Bindings).

translate_body([], [], _) :- !.
translate_body([H|T], [TBH|TBT], Bindings) :-
	translate_body(H, TBH, Bindings),
	translate_body(T, TBT, Bindings),!.
translate_body(X, X, _) :-
	atomic(X),!.
translate_body(var(X), TB, Bindings) :-
	member((var(X),TB), Bindings), !.
translate_body(Expr, TB, Bindings) :-
	nonvar(Expr),!,
	Expr =.. L,
	(length(L,1),!;
	translate_body(L, L1, Bindings),
	nonvar(L1),!,
	TB =.. L1, !).

translate(cl(Head, Body, []), Clause) :-
	translate_head(Head, TransHead, Bindings, PatternMatcher),
	translate_body(Body, TransBody, Bindings),
	Clause = (:-(def(TransHead, TransBody),PatternMatcher)).

translate_clauses([]).
translate_clauses([H|T]) :- 
	translate(H, Def),
	assertz(Def),
	translate_clauses(T).

step(app(X,Y), R) :-
	X =.. [constr|L],
	append(L, [Y], L1),
	R =.. [constr|L1], !.

step(X, Y) :-
	X =.. [constr|L],
	append(A,[E|B], L),
	step(E, E1), !,
	append(A,[E1|B], L1),
	Y =.. [constr|L1], !.
	%L \= L1.

step(X,Y) :- def(X, Y), !.
step(app(lam(Var, Expr), Arg), Expr1) :- translate_body(Expr, Expr1, [(Var, Arg)]).
step(Expr, Expr1) :-
	Expr =.. [BinOp, X, Y],
	member(BinOp, [+,-, *, div, mod]),
	(red_to_hnf(X,X1), Expr1 =.. [BinOp, X1, Y],!;
	red_to_hnf(Y,Y1), Expr1 =.. [BinOp, X, Y1]),!.
step(+(constr(X), constr(Y)), constr(Z)) :- Z is X+Y,!.
step(-(constr(X), constr(Y)), constr(Z)) :- Z is X-Y,!.
step(*(constr(X), constr(Y)), constr(Z)) :- Z is X*Y,!.
step(div(constr(X), constr(Y)), constr(Z)) :- Z is X div Y,!.
step(mod(constr(X), constr(Y)), constr(Z)) :- Z is X mod Y,!.
step(=(X,Y), constr('True')) :- X=Y, !.
step(/=(X,Y), constr('True')) :- X\=Y, !.
step(<(constr(X), constr(Y)), constr('True')) :- X<Y,!.
step(>(constr(X), constr(Y)), constr('True')) :- X>Y,!.
step(=<(constr(X), constr(Y)), constr('True')) :- X=<Y,!.
step(>=(constr(X), constr(Y)), constr('True')) :- X>=Y,!.
step(=(_,_), constr('False')).
step(/=(_,_), constr('False')).
step(<(constr(_), constr(_)), constr('False')).
step(>(constr(_), constr(_)), constr('False')).
step(=<(constr(_), constr(_)), constr('False')).
step(>=(constr(_), constr(_)), constr('False')).

step(app(X,Y), app(Z, Y)) :- step(X,Z), !.
%step(app(X,Y), app(X, Z)) :- step(Y,Z), !.
red(X,Y) :- step(X, Y).
red(X,Y) :- step(X, Z), red(Z,Y).

hnf(Term) :- atomic(Term).
hnf(Term) :-
	Term =.. [constr|L],
	forall(member(T, L),
	hnf(T)).

red_to_hnf_list([], []).
red_to_hnf_list([H|T], [H|T1]) :- hnf(H), !, red_to_hnf_list(T, T1).
red_to_hnf_list([H|T], [H1|T1]) :- red_to_hnf(H, H1), red_to_hnf_list(T, T1).

red_to_hnf(X,Y) :- red(X,Y), hnf(Y).

red_to_hnf2(X,X) :- hnf(X), !.
red_to_hnf2(X,Y) :- red_to_hnf(X,Y).

red_to_constr(X, X) :- X =.. [constr|_], !.
red_to_constr(X, Y) :- red(X,Y), Y =.. [constr|_], !.

init_counter :- assertz(next_nr(0)).
get_next_nr(N) :-
	next_nr(N1),
	N is N1+1,
	Term =.. [next_nr, N1],
	NewTerm =.. [next_nr, N],
	retract(Term),
	assertz(NewTerm).

globalize_clause(cl(Head, Body, LD), [(var(Name),var(NewName))|Bindings], GlobalizedClauses, N) :-
	Head =.. [clh, var(Name)|_],
	%get_next_nr(N),
	atomic_list_concat([Name, N], '-', NewName),
	N1 is N+1,
	globalize_clause(LD, Bindings, GlobalizedClauses1, N1),
	translate_body(Body, TransBody, Bindings),
	%translate_body(Head, TransHead, [(var(Name),var(NewName))|Bindings]),
	translate_body(GlobalizedClauses1, GlobalizedClauses2, Bindings),
	GlobalizedClauses = [cl(Head, TransBody, [])|GlobalizedClauses2].

globalize_clause([], [], [], _).
globalize_clause([H|T], Bindings, GlobalizedClauses, N) :-
	globalize_clause(H, Bindings1, GlobalizedClauses1, N),
	globalize_clause(T, Bindings2, GlobalizedClauses2, N),
	append(Bindings1, Bindings2, Bindings),
	append(GlobalizedClauses1, GlobalizedClauses2, GlobalizedClauses),!.

interp(P) :-
	lexer(Tokens, P, []),
	program(Clauses, Tokens, []),
	globalize_clause(Clauses, _, Clauses1, 0),
	translate_clauses(Clauses1),!.

eval(E, X) :-
	lexer(Tokens, E, []),
	expr(Expr, Tokens, []),
	red(Expr, X),
	hnf(X),!.

:- begin_tests(interpreter).
	test(translate_body) :-
		translate_body(cl(clh(var(bar)), constr(2), []), T, [(var(bar),var(foo))]),
		T = cl(clh(var(foo)), constr(2), []).

	test(loading) :- 
		interp("if True x y = x; if False x y = y; and x y = if x y False; or x y = if x True y; not x = if x False True; "),
		interp("reverse = rev Nil where { rev a Nil = a; rev a (Cons x xs) = rev (Cons x a) xs; } length = len 0 where { len n Nil = n; len n (Cons x xs) = len (n+1) xs; } append Nil ys = ys; append (Cons x xs) ys = Cons x (append xs ys); even Nil = True; even (Cons x Nil) = False; even (Cons x (Cons y ys)) = even ys; head (Cons x xs) = x; tail (Cons x xs) = xs; "),
		interp("app f g x = f (g x); curry f x y = f (Pair x y); uncurry g (Pair x y) = g x y; map f Nil = Nil; map f (Cons x xs) = Cons (f x) (map f xs); foldr f c Nil = c; foldr f c (Cons x xs) = f x (foldr f c xs); sort = foldr ins Nil where { ins x Nil = Cons x Nil; ins x (Cons y ys) = if (x < y) (Cons x (Cons y ys)) (Cons y (ins x ys)); }"),
		interp("iterate f a = Cons a (iterate f (f a)); filter p Nil = Nil; filter p (Cons x xs) = if (p x) (Cons x ys) ys where ys = filter p xs; enumFrom n = Cons n (enumFrom (n+1)); primes = map head (iterate sieve (enumFrom 2)) where{ sieve (Cons x xs) = filter (\\ y -> y mod x /= 0) xs;}"),
		interp("zipWith f Nil ys = Nil; zipWith f xs Nil = Nil; zipWith f (Cons x xs) (Cons y ys) = Cons (f x y) (zipWith f xs ys);"),
		interp("sum x y = x+y;fib = Cons 1 (Cons 1 (zipWith sum fib (tail fib)));"),
		interp("drop n Nil = Nil; drop 0 x = x; drop n (Cons x xs) = drop (n-1) xs;").
	test(calculations) :-
		eval("5+5", constr(10)),
		eval("5+5*5", constr(30)),
		eval("(5+5)*(5+5)", constr(100)),
		eval("1-1-1", constr(-1)).
	test(strictness) :-
		interp("loop = loop;"),
		eval("if True 7 loop", constr(7)).
	test(factorial) :-
		interp("fac 0 = 1;fac n = n*(fac(n-1));"),
		eval("fac 5", constr(120)).
	test(head_tail) :-
		eval("head (Cons 1 Nil)", constr(1)),
		eval("tail (Cons 1 Nil)", constr('Nil')).
	test(length_reverse_append) :-
		eval("reverse (Cons 1 (Cons 2 (Cons 3 Nil)))", R),
		eval("append (Cons 3 (Cons 2 Nil)) (Cons 1 Nil)", R1),
		R = constr('Cons', constr(3), constr('Cons', constr(2), constr('Cons', constr(1), constr('Nil')))),
		R1 = R,
		eval("length (Cons 1 (Cons 2 (Cons 3 Nil)))", constr(3)).
	test(lambda_expr) :-
		eval("(\\x -> x+2) 3", constr(5)).
	test(map) :-
		%interp("map f Nil = Nil;map f (Cons x xs) = Cons (f x) (map f xs);"),
		eval("map (\\ x -> x+2) (Cons 2 (Cons 1 Nil))", R),
		R = constr('Cons', constr(4), constr('Cons', constr(3), constr('Nil'))).
	test(enumFrom) :-
		%interp("enumFrom n = Cons n (enumFrom (n+1));"),
		eval("head(tail(tail((enumFrom 7))))", constr(9)),
		eval("head(tail(tail((map (\\ x -> x+x) (enumFrom 7)))))", constr(18)).
	test(pattern_matching) :-
		interp("pm 3 = 7; pm n = 0;"),
		eval("pm (1+1+1)", constr(7)).
	test(sort) :-
		eval("sort (Cons 2 (Cons 3 (Cons 1 Nil)))",Q),
		Q = constr('Cons', constr(1), constr('Cons', constr(2), constr('Cons', constr(3), constr('Nil')))),!.
	test(idlist) :-
		interp("idlist = foldr Cons Nil;"),
		eval("idlist (Cons 1 (Cons 2 (Cons 3 Nil)))", Q),
		Q = constr('Cons', constr(1), constr('Cons', constr(2), constr('Cons', constr(3), constr('Nil')))),!.
	test(fib) :-
		eval("head(drop 6 fib)", constr(13)).
:- end_tests(interpreter).
