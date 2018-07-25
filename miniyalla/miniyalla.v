(* miniyalla library for LL proof checking *)
(* Olivier Laurent *)



Require Export List.
Export ListNotations.
Require Import CMorphisms.

Require Import List_more.
Require Import Permutation_Type_more.
Require Export Permutation_Type_solve.
Require Export genperm_Type.

(** ** Definition and main properties of formulas *)

(** A set of atoms for building formulas *)
Definition Atom : Set := nat.

(** Formulas *)
Inductive formula : Set :=
| var : Atom -> formula
| covar : Atom -> formula
| one : formula
| bot : formula
| tens : formula -> formula -> formula
| parr : formula -> formula -> formula
| zero : formula
| top : formula
| aplus : formula -> formula -> formula
| awith : formula -> formula -> formula
| oc : formula -> formula
| wn : formula -> formula.

(** Orthogonal / dual of a [formula] *)

(** (the dual of [tens] and [parr] is the one compatible with non-commutative systems) *)
Fixpoint dual A :=
match A with
| var x     => covar x
| covar x   => var x
| one       => bot
| bot       => one
| tens A B  => parr (dual B) (dual A)
| parr A B  => tens (dual B) (dual A)
| zero      => top
| top       => zero
| aplus A B => awith (dual A) (dual B)
| awith A B => aplus (dual A) (dual B)
| oc A      => wn (dual A)
| wn A      => oc (dual A)
end.




(** ** Fragments for proofs *)

(** Parameters for [ll] provability:
 - [pcut], [pmix0] and [pmix2] determine whether the corresponding rule is in the system or not;
 - [pperm] is [false] for exchange rule modulo cyclic permutations and [true] for exchange rule modulo arbitrary permutations;
 - [pgax] determines the sequents which are valid as axioms in proofs.
*)
Record pfrag := mk_pfrag {
  pcut : bool ;
  pgax : { ptypgax : Type & ptypgax -> list formula } ; (* Many thanks to Damien Pous! *)
  pmix0 : bool ;
  pmix2 : bool ;
  pperm : bool }.




(** ** Rules *)

(** The main predicate: [ll] proofs.

The [nat] parameter is a size of proofs.
Choices between [plus] and [max] in binary cases are determined by the behavious in cut elimination.

All rules have their main formula at first position in the conclusion.
 - [ax_r]: identity rule restricted to propositional variables (general case proved later)
 - [ex_r]: exchange rule (parametrized by [pperm P] to determine allowed permutations)
 - [mix0_r]: nullary linear mix rule (available only if [pmix0 P = true])
 - [mix2_r]: binary linear mix rule (the order of lists is matched with the [tens_r] case) (available only if [pmix2 P = true])
 - [one_r]: one rule
 - [bot_r]: bot rule
 - [tens_r]: tensor rule (the order of lists is imposed by the cyclic permutation case)
 - [parr_r]: par rule
 - [top_r]: par rule
 - [plus_r1]: plus left rule
 - [plus_r2]: plus right rule
 - [with_r]: with rule
 - [oc_r]: promotion rule (standard shape)
 - [de_r]: dereliction rule
 - [wk_r]: weakening rule
 - [co_r]: contraction rule with [wn] context inserted between principal formulas to be general enough in the cyclic permutation case
 - [cut_r]: cut rule (the order of lists is matched with the [tens_r] case) (available only if [pcut P = true])
 - [gax_r]: generic axiom rule (parametrized by the predicate [pgax P] over sequents)
*)
Inductive ll P : list formula -> Type :=
| ax_r : forall X, ll P (covar X :: var X :: nil)
| ex_r : forall l1 l2, ll P l1 -> PCperm_Type (pperm P) l1 l2 -> ll P l2
| mix0_r {f : pmix0 P = true} : ll P nil
| mix2_r {f : pmix2 P = true} : forall l1 l2, ll P l1 -> ll P l2 ->
                         ll P (l2 ++ l1)
| one_r : ll P (one :: nil)
| bot_r : forall l, ll P l -> ll P (bot :: l)
| tens_r : forall A B l1 l2, ll P (A :: l1) -> ll P (B :: l2) ->
                                   ll P (tens A B :: l2 ++ l1)
| parr_r : forall A B l, ll P (A :: B :: l) -> ll P (parr A B :: l)
| top_r : forall l, ll P (top :: l)
| plus_r1 : forall A B l, ll P (A :: l) -> ll P (aplus A B :: l)
| plus_r2 : forall A B l, ll P (A :: l) -> ll P (aplus B A :: l)
| with_r : forall A B l, ll P (A :: l) -> ll P (B :: l) ->
                               ll P (awith A B :: l)
| oc_r : forall A l, ll P (A :: map wn l) -> ll P (oc A :: map wn l)
| de_r : forall A l, ll P (A :: l) -> ll P (wn A :: l)
| wk_r : forall A l, ll P l -> ll P (wn A :: l)
| co_r : forall A lw l, ll P (wn A :: map wn lw ++ wn A :: l) ->
                          ll P (wn A :: map wn lw ++ l)
| cut_r {f : pcut P = true} : forall A l1 l2,
    ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1)
| gax_r : forall a, ll P (projT2 (pgax P) a).

Instance ll_perm {P} : Proper ((@PCperm_Type _ (pperm P)) ==> Basics.arrow) (ll P).
Proof.
intros l1 l2 HP pi.
eapply ex_r ; eassumption.
Qed.



(** *** Variants of rules *)

(** Tactics for exchange rule *)

Ltac ex_rot :=
  eapply ex_r ; [ | symmetry ; apply PCperm_Type_last ] ; simpl.

Ltac perm_Type_solve_hypfree :=
  match goal with
  | |- Permutation_Type _ _ =>
    list_simpl ;
    cons2app_all ;
    try apply Permutation_Type_app_tail ;
    try apply Permutation_Type_app_middle ;
    try perm_Type_run ;
    apply Permutation_Type_sym ;
    perm_Type_run ; fail 
  end
with perm_Type_run :=
  do 40 (
  cons2app ;
  rewrite <- ? app_assoc ;
  try apply Permutation_Type_app_head ;
  match goal with
  | |- Permutation_Type _ _ => apply Permutation_Type_refl
  | |- Permutation_Type (_ ++ _) _ => apply Permutation_Type_app_comm
  | |- Permutation_Type (_ ++ _ ++ _) _ => perm_Type_rot
  | |- Permutation_Type (_ ++ _ ) _ => eapply Permutation_Type_trans ;
                                  [ apply Permutation_Type_app_comm
                                  | instantiate ]
  | _ => idtac
  end ).

Ltac ex_solve l :=
  apply (ex_r _ l) ; [ | simpl ; perm_Type_solve_hypfree ].

(** Weakening on a list of formulas *)
Lemma wk_list_r {P} : forall l l', ll P l' -> ll P (map wn l ++ l').
Proof with try assumption.
induction l ; intros l' H...
apply IHl in H.
apply wk_r...
Qed.

(** Contraction on a list of formulas *)
Lemma co_list_r {P} : forall l lw l',
  ll P (map wn l ++ map wn lw ++ map wn l ++ l') ->
    ll P (map wn l ++ map wn lw ++ l').
Proof with try assumption.
induction l ; intros lw l' H...
simpl in H.
rewrite app_assoc in H.
rewrite <- map_app in H.
apply co_r in H.
rewrite map_app in H.
eapply (ex_r _ _
  (map wn l ++ map wn lw ++ map wn l ++ l' ++ wn a :: nil))
  in H...
- apply IHl in H.
  eapply ex_r ; [ apply H | ].
  simpl.
  etransitivity ; [ | symmetry ; apply PCperm_Type_last ].
  rewrite <- ? app_assoc.
  reflexivity.
- rewrite ? app_assoc.
  etransitivity ; [ | apply PCperm_Type_last ].
  reflexivity.
Qed.

(** More standard shape of contraction rule with adjacent principal formulas

(this is stricly weaker than [co_r] in the case of cyclic permutations only). *)
Lemma co_std_r {P} : forall A l,
  ll P (wn A :: wn A :: l) -> ll P (wn A :: l).
Proof.
intros A l pi.
change (wn A :: l) with (wn A :: map wn nil ++ l).
apply co_r.
assumption.
Qed.

(** Standard contraction rule on a list of formulas *)
Lemma co_std_list_r {P} : forall l l',
  ll P (map wn l ++ map wn l ++ l') -> ll P (map wn l ++ l').
Proof.
intros l l' pi.
change (map wn l ++ l') with (map wn l ++ map wn nil ++ l').
eapply co_list_r.
eassumption.
Qed.

(** Axiom expansion *)
Lemma ax_exp {P} : forall A, ll P (A :: dual A :: nil).
Proof.
induction A ; simpl.
- eapply ex_r ; [ | apply PCperm_Type_swap ].
  apply ax_r.
- apply ax_r.
- eapply ex_r ; [ | apply PCperm_Type_swap ].
  apply bot_r.
  apply one_r.
- apply bot_r.
  apply one_r.
- eapply ex_r ; [ | apply PCperm_Type_swap ].
  apply parr_r.
  eapply ex_r ; [ | ].
  apply (tens_r _ _ _ _ _ IHA1 IHA2).
  etransitivity ; [ apply PCperm_Type_last | ].
  reflexivity.
- apply parr_r.
  eapply ex_r ; [ | ].
  apply tens_r.
  eapply ex_r ; [ apply IHA2 | apply PCperm_Type_swap ].
  eapply ex_r ; [ apply IHA1 | apply PCperm_Type_swap ].
  etransitivity ; [ apply PCperm_Type_last | ].
  reflexivity.
- eapply ex_r ; [ | apply PCperm_Type_swap ].
  apply top_r.
- apply top_r.
- eapply plus_r1 in IHA1.
  eapply plus_r2 in IHA2.
  eapply ex_r ; [ | ].
  apply with_r.
  eapply ex_r ; [ apply IHA1 | apply PCperm_Type_swap ].
  eapply ex_r ; [ apply IHA2 | apply PCperm_Type_swap ].
  etransitivity ; [ apply PCperm_Type_last | ].
  reflexivity.
- apply with_r ; (eapply ex_r ; [ | apply PCperm_Type_swap ]).
  + apply plus_r1 ; eapply ex_r ; [ apply IHA1 | apply PCperm_Type_swap ].
  + apply plus_r2 ; eapply ex_r ; [ apply IHA2 | apply PCperm_Type_swap ].
- change (oc A :: wn (dual A) :: nil)
    with (oc A :: map wn (dual A :: nil)).
  apply oc_r.
  eapply ex_r ; [ | ].
  apply de_r.
  eapply ex_r ; [ apply IHA | apply PCperm_Type_swap ].
  apply PCperm_Type_swap.
- eapply de_r in IHA.
  eapply ex_r ; [ | apply PCperm_Type_swap ].
  change (oc (dual A) :: wn A :: nil)
    with (oc (dual A) :: map wn (A :: nil)).
  apply oc_r.
  eapply ex_r ; [ apply IHA | apply PCperm_Type_swap ].
Qed.



(** * Some Fragments *)

Definition Empty_fun {A} : Empty_set -> A := fun o => match o with end.
Definition NoAxioms := (existT (fun x => x -> list formula) _ Empty_fun).

(** ** Standard cut-free linear logic: [ll_ll] (no mix, no axiom, no cut) *)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_ll :=  mk_pfrag false NoAxioms false false true.
(*                               cut   axioms   mix0  mix2  perm  *)

Definition ll_ll := ll pfrag_ll.


(** ** Standard linear logic with cut: [ll_cut] (no mix, no axiom) *)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_ll_cut :=  mk_pfrag true NoAxioms false false true.
(*                                   cut  axioms   mix0  mix2  perm  *)

Definition ll_cut := ll pfrag_ll_cut.



