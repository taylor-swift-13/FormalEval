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
  [-4; 8; 3; -6; 0; 6; 2; 1; 8; 14; 6; 6; -8; 14; 0] 
  [-8; 8; 3; -6; 0; 6; -4; 1; 8; 2; 6; 6; 14; 14; 0].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length *)
    simpl. reflexivity.
  - split.
    + (* 2. indices *)
      intros i H.
      (* Check each index from 0 to 14 *)
      do 15 (destruct i; [ simpl in *; try congruence | ]).
      (* For i >= 15, both are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation *)
        simpl.
        (* Goal: Permutation [-8; -6; -4; 2; 14] [-4; -6; 2; 14; -8] *)
        apply Permutation_sym.
        (* Goal: Permutation [-4; -6; 2; 14; -8] [-8; -6; -4; 2; 14] *)
        transitivity (-8 :: [-4; -6; 2; 14]).
        { (* Move -8 to front *)
          change ([-4; -6; 2; 14; -8]) with ([-4; -6; 2; 14] ++ [-8]).
          apply Permutation_sym. apply Permutation_middle. }
        { apply Permutation_cons.
          (* Goal: Permutation [-4; -6; 2; 14] [-6; -4; 2; 14] *)
          transitivity (-6 :: [-4; 2; 14]).
          { (* Move -6 to front *)
            change ([-4; -6; 2; 14]) with ([-4] ++ -6 :: [2; 14]).
            apply Permutation_sym. apply Permutation_middle. }
          { apply Permutation_cons. apply Permutation_refl. }
        }
      * (* 4. Sorted *)
        simpl.
        repeat constructor.
Qed.