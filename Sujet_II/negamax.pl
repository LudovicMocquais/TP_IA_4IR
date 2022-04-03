	/*
	Ce programme met en oeuvre l'algorithme Minmax (avec convention
	negamax) et l'illustre sur le jeu du TicTacToe (morpion 3x3)
	*/
	
:- [tictactoe].


	/****************************************************
  	ALGORITHME MINMAX avec convention NEGAMAX : negamax/5
  	*****************************************************/

	/*
	negamax(+J, +Etat, +P, +Pmax, [?Coup, ?Val])

	SPECIFICATIONS :

	retourne pour un joueur J donne, devant jouer dans
	une situation donnee Etat, de profondeur donnee P,
	le meilleur couple [Coup, Valeur] apres une analyse
	pouvant aller jusqu'a la profondeur Pmax.

	Il y a 3 cas a decrire (donc 3 clauses pour negamax/5)
	
	1/ la profondeur maximale est atteinte : on ne peut pas
	developper cet Etat ; 
	il n'y a donc pas de coup possible a jouer (Coup = rien)
	et l'evaluation de Etat est faite par l'heuristique.

	2/ la profondeur maximale n'est pas  atteinte mais J ne
	peut pas jouer ; au TicTacToe un joueur ne peut pas jouer
	quand le tableau est complet (totalement instancie) ;
	il n'y a pas de coup a jouer (Coup = rien)
	et l'evaluation de Etat est faite par l'heuristique.

	3/ la profondeur maxi n'est pas atteinte et J peut encore
	jouer. Il faut evaluer le sous-arbre complet issu de Etat ; 

	- on determine d'abord la liste de tous les couples
	[Coup_possible, Situation_suivante] via le predicat
	 successeurs/3 (deja fourni, voir plus bas).

	- cette liste est passee a un predicat intermediaire :
	loop_negamax/5, charge d'appliquer negamax sur chaque
	Situation_suivante ; loop_negamax/5 retourne une liste de
	couples [Coup_possible, Valeur]

	- parmi cette liste, on garde le meilleur couple, c-a-d celui
	qui a la plus petite valeur (cf. predicat meilleur/2);
	soit [C1,V1] ce couple optimal. Le predicat meilleur/2
	effectue cette selection.

	- finalement le couple retourne par negamax est [Coup, V2]
	avec : V2 is -V1 (cf. convention negamax vue en cours).

A FAIRE : ECRIRE ici les clauses de negamax/5
.....................................
	*/
	negamax(J, Etat, Pmax, Pmax, [rien, Val]):-
		heuristique(J,Etat,Val), !.

	
	negamax(J, Etat, P, Pmax, [rien, Val]):-
		situation_terminale(J,Etat),
		heuristique(J,Etat,Val), !.
		

	negamax(J, Etat, P, Pmax, [Coup, Val]):-
		successeurs(J,Etat,Succ),
		loop_negamax(J,P,Pmax,Succ,SuccF),
		meilleur(SuccF,[Coup,Val1]),
		Val is -Val1.




	/*******************************************
	 DEVELOPPEMENT D'UNE SITUATION NON TERMINALE
	 successeurs/3 
	 *******************************************/

	 /*
   	 successeurs(+J,+Etat, ?Succ)

   	 retourne la liste des couples [Coup, Etat_Suivant]
 	 pour un joueur donne dans une situation donnee 
	 */

successeurs(J,Etat,Succ) :-
	copy_term(Etat, Etat_Suiv),
	findall([Coup,Etat_Suiv],
		    successeur(J,Etat_Suiv,Coup),
		    Succ).

	/*************************************
         Boucle permettant d'appliquer negamax 
         a chaque situation suivante :
	*************************************/

	/*
	loop_negamax(+J,+P,+Pmax,+Successeurs,?Liste_Couples)
	retourne la liste des couples [Coup, Valeur_Situation_Suivante]
	a partir de la liste des couples [Coup, Situation_Suivante]
	*/

loop_negamax(_,_, _  ,[],                []).
loop_negamax(J,P,Pmax,[[Coup,Suiv]|Succ],[[Coup,Vsuiv]|Reste_Couples]) :-
	loop_negamax(J,P,Pmax,Succ,Reste_Couples), %appel recursif pour developper le reste des successeurs de la liste
	adversaire(J,A), % Trouve l'adversaire du joueur courant car negamax est relatif au joueur courant
	Pnew is P+1, %on augmente la profondeur car on a explore le niveau courant on passe donc au suivant
	negamax(A,Suiv,Pnew,Pmax, [_,Vsuiv]). % on developpe l'etat suivant (c'est l'adversaire qui joue le prochain 
											%coup) de la liste initiale pour calculer la valeur finale apres le 
											%developpement (successions des coups) jusqu'a la profondeur 
											%maximale

	/*

A FAIRE : commenter chaque litteral de la 2eme clause de loop_negamax/5,
	en particulier la forme du terme [_,Vsuiv] dans le dernier
	litteral ?
	*/

	/*********************************
	 Selection du couple qui a la plus
	 petite valeur V 
	 *********************************/

	/*
	meilleur(+Liste_de_Couples, ?Meilleur_Couple)

	SPECIFICATIONS :
	On suppose que chaque element de la liste est du type [C,V]
	- le meilleur dans une liste a un seul element est cet element
	- le meilleur dans une liste [X|L] avec L \= [], est obtenu en comparant
	  X et Y,le meilleur couple de L 
	  Entre X et Y on garde celui qui a la petite valeur de V.

A FAIRE : ECRIRE ici les clauses de meilleur/2
	*/

	meilleur([C],C).

	meilleur([X|L], M):-
		not(L == []),
		meilleur_rec(L,X,M).

	
	meilleur_rec([],M,M).
	meilleur_rec([[C,V]|L],[Ci,Vi],M):-
		V < Vi,
		meilleur_rec(L,[C,V],M).
	
	meilleur_rec([[C,V]|L],[Ci,Vi],M):-
		Vi =< V,
		meilleur_rec(L,[Ci,Vi],M).




	/******************
  	PROGRAMME PRINCIPAL
  	*******************/

main(B,V, Pmax) :- %Donne le premier coup à jouer avec une profondeur de recherche de Pmax coups
	situation_initiale(U0),
	joueur_initial(J),
	negamax(J,U0,0,Pmax,[B,V]).

%mainv2(J,U,B,V, Pmax) :- %% Pour simuler tout le jeu étape par étape plus facilement
%	negamax(J,U,0,Pmax,[B,V]).

	/*
A FAIRE :
	Compl�ter puis tester le programme principal pour plusieurs valeurs de la profondeur maximale.
	Pmax = 1, 2, 3, 4 ...
	Commentez les r�sultats obtenus.
	*/

plusieurs_profondeurs(0,[]).
plusieurs_profondeurs(P,[[P,B,V,Runtime]|L]):- %boucle retournant une liste avec les coups et les valeurs associées à chaque profondeur
	P>0,
	P2 is P-1,
	statistics(runtime,[Start,_]),
	main(B,V,P),
	statistics(runtime,[Stop,_]),
	Runtime is Stop -Start,
	plusieurs_profondeurs(P2, L).

test(L):- 
	plusieurs_profondeurs(9,L).
