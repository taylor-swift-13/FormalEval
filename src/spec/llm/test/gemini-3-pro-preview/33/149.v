Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Example test_case : sort_third_spec 
  [1; 2; 3; -3; 5; 1; 0; 4; 9; -12; 7; 6] 
  [-12; 2; 3; -3; 5; 1; 0; 4; 9; 1; 7; 6].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 12 (destruct i; [
        simpl in *;
        try (match goal with | H : ?X <> ?X |- _ => contradiction H end);
        try reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply NoDup_Permutation.
        -- repeat constructor; simpl; try lia; try (intro C; decompose [or] C; discriminate).
        -- repeat constructor; simpl; try lia; try (intro C; decompose [or] C; discriminate).
        -- intros x. split; intro H; simpl in *; decompose [or] H; subst; auto.
      * simpl.
        repeat constructor; simpl; try lia.
Qed.