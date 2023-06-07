(* begin hide *)
Require Import List Arith Lia.
(* end hide *)

(** * Introdução *)

(**  a fazer *)

(** * Formalização *)

(** Inicialmente definiremos o tamanho de um par de listas de naturais. Isto será importante para ser utilizado como garantia da boa definição da função recursiva [merge].
*)

Definition len (p: list nat * list nat) := length (fst p) + length (snd p).

(* begin hide *)
Require Import Recdef Sorted Permutation.
(* end hide *)

(** A função [merge] a seguir recebe um par de listas de naturais como argumento e, retorna uma lista ordenada contendo todos os elementos do par, desde que cada lista do par esteja ordenada.
 *)

Function merge (p : list nat * list nat) {measure len p} : list nat :=
  match p with
  | (nil, l2) => l2
  | (l1, nil) => l1
  | (h1::tl1,h2::tl2) => if h1 <=? h2 then h1::(merge (tl1,h2::tl2)) else h2::(merge (h1::tl1,tl2)) end.                                        
Proof.
  - intros. unfold len. auto.
  - intros. unfold len. simpl. lia.
Defined.

(**
 Utilizaremos a noção de ordenação dada pela seguinte definição indutiva:
 *)

Inductive sorted :list nat -> Prop :=
| sorted_nil: sorted nil
| sorted_one: forall x, sorted (x::nil)
| sorted_all: forall x y l, x <= y -> sorted (y::l) -> sorted (x::y::l).

(** A definição [sorted] possui três regras (de inferência):
 %\begin{enumerate}
  \item a primeira, chamada $sorted\_nil$, diz que a lista vazia está ordenada;
  \item a segunda, chamada $sorted\_one$, diz que listas unitárias estão ordenadas;
  \item por fim, a terceira regra ($sorted\_all$) diz que se $x \leq y$ e a lista $(y::l)$ está ordenada então a lista $(x::y::l)$ está ordenada. Em outras palavras, uma lista com pelo menos dois elementos está ordenada se ...
 \end{enumerate}% *)

(* Theorem merge_sorts: forall l1 l2, sorted l1 -> sorted l2 -> sorted (merge (l1,l2)).
Proof.
  intros l1 l2. remember (l1,l2) as p.
  assert (H: fst p = l1). {
    rewrite Heqp. simpl. reflexivity.
  }
  rewrite <- H.
  functional induction (merge (l1,l2)).
-  
  Admitted.
 OU 

Lemma ex: forall p q r: Prop, (p -> q -> r) <-> ((p /\ q) -> r).
Proof.
  intros p q r. split.
  - intro H. intro H1. apply H; apply H1.
  - intro H. intro H1. intro H2. apply H. split; assumption.
Qed. *)    

Definition le_all x l := forall y, In y l -> x <= y.

Lemma le_all_sorted: forall h l, le_all h l -> sorted l -> sorted (h::l).
Proof.
Admitted.

Lemma le_all_merge: forall l1 l2 h, le_all h l1 -> le_all h l2 -> le_all h (merge (l1,l2)).
Proof.
  Admitted.

(* ou *)

Lemma le_all_merge_app: forall l1 l2 h, le_all h (l1 ++ l2) -> le_all h (merge (l1,l2)).
Proof.
  Admitted.


Theorem merge_sort: forall p, sorted (fst p) -> sorted (snd p) -> sorted (merge p).
Proof.
  (** %{\bf Prova.}% A prova é por indução na estrutura da função [merge]. Portanto, temos 4 casos:
    %\begin{enumerate}
  \item No primeiro caso, o primeiro elemento do par é a lista vazia, a função $merge$ retorna o segundo elemento do par, que por hipótese está ordenado;
  \item O segundo caso é análogo ao caso anterior, exceto pelo fato de que  a função $merge$ retorna o primeiro elemento do par, que por hipótese também está ordenado;
  \item No terceiro caso, as duas listas são não vazias, digamos $fst\ p = h_1::tl_1$ e $snd\ p = h_2::tl_2$, e $h_1 \leq h_2$. Temos que provar que a lista $h_1::merge(tl_1,h_2::tl2)$ está ordenada de acordo com a definição da função $merge$. Para isto, definimos um lema ($le\_all\_sorted$) que diz que uma lista não vazia está ordenada se o seu primeiro elemento é menor ou igual a todos os elementos da cauda, que por sua vez precisa estar ordenada. \hfill$\Box$
      \end{enumerate}% *)

  intro p. functional induction (merge p).
  - intros H1 H2. simpl in *. exact H2.
  - intros H1 H2. simpl in *. exact H1.
  - intros H1 H2. simpl in *. apply le_all_sorted.
    + apply le_all_merge.
      * admit. (* ok *)
      * admit. (* ok *)
    + apply IHl.
      * inversion H1.
        ** apply sorted_nil.
        ** assumption.
      * assumption.
  - Admitted.


Function mergesort (l: list nat) {measure length l}: list nat := match l with
                                              | nil => nil
                                              | x::nil => l
                                              | h::tl => let m := ((length l)/2) in
                                                         let l1 := firstn m l in
                                                         let l2 := skipn m l in
                                                         merge (mergesort l1, mergesort l2)
                                              end.
Proof.
  - intros. rewrite skipn_length. simpl length. apply Nat.sub_lt.
    + apply Nat.div_le_upper_bound.
      * auto.
      * lia.
    + apply Nat.div_str_pos. lia.
  - intros. rewrite firstn_length_le.
    + simpl length. apply Nat.div_lt_upper_bound.
      * auto.
      * lia.
    + apply Nat.div_le_upper_bound.
      * auto.
      * lia.
Defined.


Theorem mergesort_correct: forall l, sorted (mergesort l) /\ Permutation l (mergesort l).
Proof.
  Admitted.

(** * Conclusão *)

(** * Referências (opcional) *)
