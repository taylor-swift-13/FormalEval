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
  [300%Z; 799%Z; 6%Z; 7%Z; 290%Z; 8%Z; 289%Z; 20%Z; 104%Z; -277%Z; 8%Z; 104%Z; 200%Z; -8%Z; 700%Z; 900%Z; -901%Z; 800%Z; 1000%Z; 290%Z; -8%Z; 104%Z]
  [-277%Z; 799%Z; 6%Z; 7%Z; 290%Z; 8%Z; 104%Z; 20%Z; 104%Z; 200%Z; 8%Z; 104%Z; 289%Z; -8%Z; 700%Z; 300%Z; -901%Z; 800%Z; 900%Z; 290%Z; -8%Z; 1000%Z].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 22 (destruct i as [|i]; [ simpl in *; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        assert (Hperm: forall x l l1 l2, Permutation l (l1 ++ l2) -> Permutation (x :: l) (l1 ++ x :: l2)).
        { intros. apply Permutation_trans with (x :: l1 ++ l2).
          - apply Permutation_cons. assumption.
          - apply Permutation_sym. apply Permutation_middle. }
        apply Hperm with (l1 := [300%Z; 7%Z; 289%Z]). simpl.
        apply Hperm with (l1 := [300%Z]). simpl.
        apply Hperm with (l1 := [300%Z; 289%Z; 200%Z; 900%Z; 1000%Z]). simpl.
        apply Hperm with (l1 := [300%Z; 289%Z]). simpl.
        apply Hperm with (l1 := [300%Z]). simpl.
        apply Hperm with (l1 := []). simpl.
        apply Hperm with (l1 := []). simpl.
        apply Hperm with (l1 := []). simpl.
        apply Permutation_refl.
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ (apply HdRel_cons; reflexivity) || apply HdRel_nil | ]).
        apply Sorted_nil.
Qed.