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
  [500; 9; 8; 7; 6; 5; 4; 2; 1; -1; -2; -4; -1; -5; -6; -7; -8; -9; -11] 
  [-11; 9; 8; -7; 6; 5; -1; 2; 1; -1; -2; -4; 4; -5; -6; 7; -8; -9; 500].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 19 (destruct i; [
        simpl in H;
        try (exfalso; apply H; reflexivity);
        simpl; reflexivity
      | ]).
      simpl; reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        assert (Hrev: [-11; -7; -1; -1; 4; 7; 500] = rev [500; 7; 4; -1; -1; -7; -11]) by reflexivity.
        rewrite Hrev.
        apply Permutation_sym.
        apply Permutation_rev.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat constructor; unfold Z.le; simpl; intros; discriminate.
Qed.