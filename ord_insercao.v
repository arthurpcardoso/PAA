(** Algoritmo de Ordenação por Inserção em listas *)

From Coq Require Import List Arith.
Open Scope nat_scope.

(** * Definição de ordenação *)

Inductive ordenada: list nat -> Prop :=
| lista_vazia: ordenada nil
| lista_unit: forall x, ordenada (x :: nil)
| lista_mult: forall x y l, x <= y -> ordenada (y :: l) -> ordenada (x :: y :: l).

(** * Definição da função de inserção *)

Fixpoint insere (n:nat) (l: list nat) :=
  match l with
  | nil => n :: nil
  | h :: tl => if n <=? h then (n :: l)
             else (h :: (insere n tl)) 
                      end.

(** * Definição da função principal do algoritmo. *)

 Fixpoint ord_insercao l :=
  match l with
    | nil => nil
    | h :: tl => insere h (ord_insercao tl)
  end.

(** A função [insert] preserva a ordenação. *)

Lemma insere_preserva_ordem: forall l x, ordenada l -> ordenada (insere x l). 
Proof.
 induction l.
 - intros x Hnil.
   simpl.
   apply lista_unit.
 - intros x H.
   simpl.
   destruct (x<=?a) eqn:Hle.
   + apply lista_mult.
     * apply leb_complete.
       assumption.
     * assumption.
   + apply leb_complete_conv in Hle.
     case_eq l.
     * intro Hnil.
       simpl.
       apply lista_mult.
       auto with arith.
       apply lista_unit.
     * intros n l' Hl'.
       subst.
       simpl in *.
       inversion H; subst.
       destruct (x <=? n) eqn:Hle'.
       {
       apply lista_mult.
         - auto with arith.
         - apply (IHl x) in H4.
           rewrite Hle' in H4.
           assumption.
       }
       {
       apply lista_mult.
         - auto with arith.
         - apply (IHl x) in H4.
           rewrite Hle' in H4.
           assumption.
        }
 Qed.

(** O algoritmo ord_insercao ordena. *)

Lemma ord_insercao_ordena: forall l, ordenada (ord_insercao l).
Proof.
  induction l.
  - apply lista_vazia.
  - simpl.
    apply insere_preserva_ordem.
    exact IHl.
Qed.
  
(** * Permutação *)

Inductive perm: list nat -> list nat -> Prop :=
| perm_refl: forall l, perm l l
| perm_hd: forall x l l', perm l l' -> perm (x::l) (x::l')
| perm_swap: forall x y l l', perm l l' -> perm (x::y::l) (y::x::l')
| perm_trans: forall l l' l'', perm l l' -> perm l' l'' -> perm l l''.

Lemma insere_perm: forall l a, perm (a :: l) (insere a l).
Proof.
	intros.
  induction l as [|a' l']; auto.
  simpl. 
  apply perm_refl.
  apply perm_trans with (a' :: a :: l'); auto.
  apply perm_swap.
  apply perm_refl.
  simpl.
  destruct (a<=?a') eqn:Hle.
  apply perm_swap.
  apply perm_refl.
  apply perm_hd with (x:=a').
  assumption.
Qed.
  
Lemma ord_insercao_perm: forall l, perm l (ord_insercao l).
Proof.
	induction l.
  * simpl. 
  	apply perm_refl.
  * simpl.
  	apply perm_trans with (l' := a::ord_insercao l).
    apply perm_hd with (x:=a) in IHl.
    assumption.
    apply insere_perm.
Qed.    
    
Theorem correcao_ord_insercao: forall l, ordenada (ord_insercao l) /\ perm l (ord_insercao l).
Proof.
	induction l.
  	simpl.
    split.
    apply lista_vazia.
    apply perm_refl.
    split.
    apply ord_insercao_ordena.
    apply ord_insercao_perm.
Qed.
    
  	
  

  
(** Extração de código certificado *)

Require Extraction.

Recursive Extraction ord_insercao.
Extraction "ord_insercao.ml" ord_insercao.
