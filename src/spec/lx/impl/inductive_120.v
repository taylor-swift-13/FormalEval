(* HumanEval 120 - Inductive Spec *)
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Sorting.Sorted Coq.Sorting.Permutation.
Import ListNotations.
Open Scope Z_scope.

Inductive sorted_desc_rel : list Z -> list Z -> Prop :=
| sdr_nil : sorted_desc_rel nil nil
| sdr_single : forall x, sorted_desc_rel (x :: nil) (x :: nil)
| sdr_cons : forall x xs sorted_tail,
   (sorted_tail = nil \/ exists h t, sorted_tail = h :: t /\ Z.leb x h = true) ->
   sorted_desc_rel xs sorted_tail ->
   sorted_desc_rel (x :: xs) (x :: sorted_tail).

Inductive take_rel : nat -> list Z -> list Z -> Prop :=
| tr_zero : forall l, take_rel 0%nat l nil
| tr_nil : forall k, take_rel (S k) nil nil
| tr_cons : forall h t k first, take_rel k t first ->
    take_rel (S k) (h :: t) (h :: first).

Inductive sorted_asc_rel : list Z -> list Z -> Prop :=
| sar_nil : sorted_asc_rel nil nil
| sar_single : forall x, sorted_asc_rel (x :: nil) (x :: nil)
| sar_cons : forall x xs sorted_tail, 
   (sorted_tail = nil \/ exists h t, sorted_tail = h :: t /\ Z.leb h x = true) ->
   sorted_asc_rel xs sorted_tail ->
   sorted_asc_rel (x :: xs) (x :: sorted_tail).

Definition top_k_spec (arr : list Z) (k : nat) (output : list Z) : Prop :=
  exists sorted_desc top_k_desc, Permutation arr sorted_desc /\
    sorted_desc_rel sorted_desc sorted_desc /\
    take_rel k sorted_desc top_k_desc /\
    sorted_asc_rel top_k_desc output.

