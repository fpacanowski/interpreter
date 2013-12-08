:- module(parser, [program/3, expr/3]).

begins_uppercase(Atom) :-
	atom_codes(Atom, [L|_]),
	char_type(L, upper).

program([]) --> [].
program([ClausesH|ClausesT]) --> claus(ClausesH), program(ClausesT).
clauses(X) --> claus(X).
clauses(X) --> [tkLBra], program(X), [tkRBra].
local_decl([]) --> [tkSc].
local_decl(X) --> [tkWhere], clauses(X).
claus(cl(Head, Body, LD)) --> clause_head(Head), [tkEq], expr(Body), local_decl(LD).
clause_head(X) --> variable(V), params(P), {X =.. [clh, V|P]}.
params([]) --> [].
params([ParamsH|ParamsT]) --> param(ParamsH), params(ParamsT).
param(P) --> variable(P).
param(P) --> constr(P).
param(P) --> [tkLPar], pattern(P), [tkRPar].
pattern(P) --> variable(P).
pattern(P) --> constr(Constr),  params(Params), {Constr =.. [_,ConstrName], P =.. [constr,ConstrName|Params]}.
expr(lam(Var,Body)) --> [tkLambda], variable(Var), [tkArrow], expr(Body).
expr(X) --> simple_expr(X).
expr(Expr) --> simple_expr(X), comparative_operator(Op), simple_expr(Y), {Expr =.. [Op, X, Y]}.
simple_expr(Expr) --> summand(X), simple_expr(X, Expr).
simple_expr(Acc, Expr) --> additive_operator(Op), summand(X), {Acc1 =.. [Op, Acc, X]}, simple_expr(Acc1,Expr).
simple_expr(Acc, Acc) --> [].
summand(Expr) --> application(X), summand(X, Expr).
summand(Acc, Expr) --> multiplicative_operator(Op), application(X), {Acc1 =.. [Op, Acc, X]}, summand(Acc1,Expr).
summand(Acc, Acc) --> [].
application(Expr) --> atomic_expr(X), application(X,Expr).
application(Acc, Expr) --> atomic_expr(X), {Acc1 =.. [app, Acc, X]}, application(Acc1, Expr).
application(Acc, Acc) --> [].
atomic_expr(X) --> [tkLPar], expr(X), [tkRPar].
atomic_expr(X) --> variable(X).
atomic_expr(X) --> constr(X).
variable(var(Id))  --> [tkId(Id)], {\+begins_uppercase(Id)}.
constr(constr(Id)) --> [tkId(Id)], {begins_uppercase(Id)}.
constr(constr(Nr)) --> [tkNr(Nr)].
additive_operator(+) --> [tkPlus].
additive_operator(-) --> [tkMinus].
multiplicative_operator(*) --> [tkTimes].
multiplicative_operator(div) --> [tkDiv].
multiplicative_operator(mod) --> [tkMod].
comparative_operator(<) --> [tkLT].
comparative_operator(>) --> [tkGT].
comparative_operator(=<) --> [tkLTE].
comparative_operator(>=) --> [tkGTE].
comparative_operator(=) --> [tkEq].
comparative_operator(/=) --> [tkNE].

:- begin_tests(parser).
	test(constr) :-
		constr(constr('Atom'), [tkId('Atom')], []),
		\+constr(_, [tkId('atom')], []),
		constr(constr(123),[tkNr(123)], []).
	test(application) :-
		application(app(app(var(f), var(f)), var(f)), [tkId(f), tkId(f), tkId(f)], []).
	test(additive_operators) :-
		simple_expr(var(x)-var(x)+var(x),[tkId(x),tkMinus,tkId(x),tkPlus,tkId(x)],[]).
	test(multiplicative_operators) :-
		simple_expr(var(x)*var(x)*var(x),[tkId(x),tkTimes,tkId(x),tkTimes,tkId(x)],[]).
	test(priority) :- 
		simple_expr(var(x)+var(x)*var(x),[tkId(x),tkPlus,tkId(x),tkTimes,tkId(x)],[]).
	test(parentheses) :-
		expr((var(x)+var(x))*var(x), [tkLPar, tkId(x),tkPlus,tkId(x),tkRPar,tkTimes,tkId(x)],[]).
	test(comparative_operators) :-
		expr(X, [tkLPar, tkId(x),tkPlus,tkId(x),tkRPar,tkLT,tkId(x),tkTimes,tkId(x)],[]),
		X = (var(x)+var(x)<var(x)*var(x)).
	test(building_clause) :-
		claus(cl(clh(var(foo)), constr(123),[]), [tkId(foo), tkEq, tkNr(123), tkSc], []),
		claus(cl(clh(var(foo),var(x)), var(x),[]), [tkId(foo), tkId(x), tkEq, tkId(x), tkSc], []),
		program(X, [tkId(head), tkLPar, tkId('Cons'), tkId(x), tkId(y), tkRPar, tkEq, tkId(x), tkSc], []),
		X = [cl(clh(var(head), constr('Cons', var(x), var(y))), var(x),[])].
:- end_tests(parser).
