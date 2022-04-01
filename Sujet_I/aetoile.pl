%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

/*
Rappels sur l'algorithme
 
- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu
 
   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
   rapidement le prochain etat a developper (celui qui a f(U) minimum).
   
   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
   l'etat). Il permet de retrouver facilement n'importe quel etat pendant

   On gere les 2 ensembles de fa�on synchronisee : chaque fois qu'on modifie
   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.

   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
   facilement un etat par la donnee de sa situation.
   Q est modelise par un seul arbre binaire de recherche equilibre.

Predicat principal de l'algorithme :

   aetoile(Pf,Pu,Q)

   - reussit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
	 et pour chacun
		si S appartient a Q, on l'oublie
		si S appartient a Ps (etat deja rencontre), on compare
			g(S)+h(S) avec la valeur deja calculee pour f(S)
			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
				g et f 
			sinon on ne touche pas a Pf
		si S est entierement nouveau on l'insere dans Pf et dans Ps
	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPs, NewQs

*/

%*******************************************************************************

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche   
:- ['taquin.pl'].    % predicats definissant le systeme a etudier

%*******************************************************************************

main :-
	% initialisations Pf, Pu et Q 
	initial_state(S0),
	heuristique(S0, H0),
	G0 is 0,
	F0 is (H0+G0),
	empty(Pf0), 
	empty(Pu0), 
	empty(Q),

	insert([[F0,H0,G0], S0], Pf0, Pf),
	insert([S0,[F0,H0,G0], nil,nil], Pu0, Pu),


	% lancement de Aetoile
	aetoile(Pf,Pu,Q).



%*******************************************************************************

aetoile(Pf, Ps, _) :-
%%% Cas Trivial 1
	empty(Ps),
	write('PAS de SOLUTION : L ETAT FINAL N EST PAS ATTEIGNABLE !').

aetoile(Pf, Pu,Q) :-
%%%% Cas trivial 2
	suppress_min([Cost,S],Pf,Pff),
	final_state(S),

	% On cherche le pere de la situation finale et l'action réalisee pour arriver à la situation finale
	suppress([S,Cost,Pere,ActionFinale],Pu,Puf),

	insert([S,Cost,Pere,ActionFinale],Q,Qf),

	affiche_solution(Qf).

aetoile(Pf, Ps, Qs) :-
%%%% Cas général

	% on enlève le nœud de Pf correspondant à l’état U à développer (celui de valeur F minimale) et on enlève aussi le nœud
	%frère associé dans Pu
	suppress_min([[Fu,Hu,Gu],U],Pf,Pf_int),
	suppress([U,[Fu,Hu,Gu],Pere,Action],Ps,Ps_int),

	% developpement de U
		%Determiner tous les successeurs
	expand(U,Gu,Tab_succ),
		%Traiter chaque noeud
	loop_successors(Tab_succ, Qs,Pf_int,Ps_int, Qs_int, Pf_new, Ps_new),

	% Inserer le noeud U dans Q
	insert([U,[Fu,Hu,Gu], Pere,Action], Qs_int, Qs_new),

	%Appeler recursivement aetoile
	aetoile(Pf_new,Ps_new,Qs_new).

%*******************************************************************************
% Predicats intermédiaires
%**************************

affiche_solution(Q) :-
	final_state(F),
	affiche_solution_rec(Q,F).

affiche_solution_rec(Q,U):-
	suppress([U,_,nil,Action], Q, _).

affiche_solution_rec(Q, U) :-
	suppress([U,_,Pere,Action], Q, Q_new),
	affiche_solution_rec(Q_new,Pere),
	write(" "),
	write(Action).
	

expand(U,Gu,Tab_succ):-
	findall( [Succ,[F,H,G],U, A],
			(	rule(A,Cout,U,Succ),
				heuristique(Succ,H), 
				G is (Gu+Cout), 
				F is (G+H)
			), 
			Tab_succ).



loop_successors([], Qs,Pf,Ps,Qs,Pf,Ps). %% Fin de la loop

loop_successors([ [S,[F,H,G],_,_] | Tab_succ], Qs,Pf,Ps, Q_new, Pf_new, Ps_new) :-
%% Cas ou S est dans Q -> dejà développé
	belongs([S, _,_,_], Qs),
	suppress([S, _,_,_ ],Ps,Ps_new),
	suppress([[F,H,G],S],Pf,Pf_new),
	loop_successors(Tab_succ, Qs,Pf_int,Ps_int,Q_new, Pf_new, Ps_new).

loop_successors([ [S,[F,H,G],_,_] | Tab_succ], Qs,Pf,Ps, Q_new, Pf_new, Ps_new) :-
%% Cas ou S est dans dans P, état à développer on garde la meilleur evalutation
	belongs([[F,H,G],S], Pf),
	findall( [F,H,G],
			(belongs([_,S], Pf)), 
			Eval),
	meilleur_Eval(Eval, Meilleur),
	suppress_not_meilleur(Eval,Meilleur, Ps,Pf,Ps_int, Pf_int),
	loop_successors(Tab_succ, Qs,Pf_int,Ps_int,Q_new, Pf_new, Ps_new).



loop_successors([ [S,[F,H,G],Pere,Action] | Tab_succ], Qs,Pf,Ps, Q_new, Pf_new, Ps_new) :-
%% Cas ou S est un nouvel état
	not(belongs([[F,H,G],S], Pf)),
	not(belongs([S, [F,H,G], _,_], Qs)),
	insert([S, [F,H,G], Pere,Action ], Ps, Ps_int),
	insert([[F,H,G],S], Pf, Pf_int),
	loop_successors(Tab_succ, Qs,Pf_int,Ps_int,Q_new, Pf_new, Ps_new).



meilleur_Eval_rec([], I,I).

meilleur_Eval_rec([[F1,H1,G1]| R], [X,H,G], Meilleur):-
	F1 =< X,
	meilleur_Eval_rec(R, [F1,H1,G1], Meilleur).

meilleur_Eval_rec([[F1,H1,G1]|R], [X,H,G], Meilleur):-
	F1 > X,
	meilleur_Eval_rec(R, [X,H,G], Meilleur).


meilleur_Eval([ [F1,H1,G1] | R], Meilleur):-
	meilleur_Eval_rec([ [F1,H1,G1] | R], [F1,H1,G1], Meilleur).



suppress_not_meilleur([[F1,H1,G1] | R], Meilleur, Ps,Pf,Ps_new, Pf_new):-
	not([F1,H1,G1] = Meilleur),
	suppress([S,[F1,H1,G1],_,_],Ps,Ps_int),
	suppress([[F1,H1,G1],S],Pf,Pf_int),
	suppress_not_meilleur(R, Meilleur, Ps_int, Pf_int, Ps_new, Pf_new).

suppress_not_meilleur([[F1,H1,G1] | R], Meilleur, Ps,Pf,Ps_new, Pf_new):-
	[F1,H1,G1] = Meilleur,
	suppress_not_meilleur(R, Meilleur, Ps, Pf, Ps_new, Pf_new).

suppress_not_meilleur([],Meilleur, Ps,Pf,Ps, Pf).




%*******************************************************************************
% Tests prédicats intermédiares
%********************************


test_affiche_solution :-
	final_state(F),

	rule(up,1, F, S),
	rule(right,1,S,Si),

	empty(Q0),
	insert([Si,[2,2,0],nil,nil], Q0,Q1),
	insert([S, [2,1,1],Si,left],Q1,Qf),
	insert([F, [2,0,2],S,down],Qf,Qff),
	affiche_solution(Qff).


test_expand(Tab_succ):-
	initial_state(U),
	expand(U,0, Tab_succ).

test_loop_succ(Tab_succ):-
	initial_state(U),

	heuristique(U, H0),
	G0 is 0,
	F0 is (H0+G0),
	empty(Pf0), 
	empty(Pu0), 

	empty(Q),

	insert([[F0,H0,G0], U], Pf0, Pf),
	insert([U,[F0,H0,G0], nil,nil], Pu0, Pu),

	expand(U,0, Tab_succ),
	
	loop_successors(Tab_succ, Q,Pf,Pu,Qn,Pfn,Pun),
	
	write('\nQn'),put_flat(Qn),
	write('\nPfn'),put_flat(Pfn),
	write('\nPun'),put_flat(Pun).