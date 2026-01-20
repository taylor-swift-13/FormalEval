Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
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
  [1; 2; 3; -3; 5; 1; 0; 0; 9; 0; 7; 0] 
  [-3; 2; 3; 0; 5; 1; 0; 0; 9; 1; 7; 0].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      repeat (destruct i; [ simpl in *; try (elim H; reflexivity); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        apply Permutation_sym.
        change [-3; 0; 0; 1] with ([-3; 0; 0] ++ [1]).
        apply Permutation_cons_append.
      * (* Sorted *)
        simpl.
        repeat constructor.
Qed.