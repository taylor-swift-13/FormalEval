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
  [9; 0; -200; 8; -1; -9; -3; -4; -5; 12; 9] 
  [-3; 0; -200; 8; -1; -9; 9; -4; -5; 12; 9].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check indices 0 to 11 explicitly *)
      do 12 (destruct i as [|i]; [
        simpl in H; try (exfalso; apply H; reflexivity);
        simpl; reflexivity
      | ]).
      (* For indices >= 12, both lists are exhausted *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-3; 8; 9; 12] [9; 8; -3; 12] *)
        (* Rewrite second list to expose -3 at the correct position for Permutation_cons_app *)
        change [9; 8; -3; 12] with ([9; 8] ++ -3 :: [12]).
        apply Permutation_cons_app.
        simpl.
        apply perm_swap.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Prove Z.le conditions explicitly by computing comparison *)
        repeat constructor; unfold Z.le; compute; intro C; discriminate.
Qed.