Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
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
  [300; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; -901; 800; 1000; -901; 0; 3; 6]
  [-901; 6; 7; -901; 8; 289; 4; -105; -277; 6; 200; 3; 20; 700; 900; 104; 800; 1000; 290; 0; 3; 300].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check indices 0 to 21 individually *)
      do 22 (destruct i; [ simpl in H; try congruence; simpl; reflexivity | ]).
      (* For i >= 22, both lists return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        (* Target: [-901; -901; 4; 6; 20; 104; 290; 300] *)
        (* Source: [300; 290; 20; 104; 4; -901; -901; 6] *)
        simpl.
        apply Permutation_trans with (l' := -901 :: [300; 290; 20; 104; 4] ++ [-901; 6]).
        2: apply Permutation_middle. apply Permutation_cons. simpl.
        apply Permutation_trans with (l' := -901 :: [300; 290; 20; 104; 4] ++ [6]).
        2: apply Permutation_middle. apply Permutation_cons. simpl.
        apply Permutation_trans with (l' := 4 :: [300; 290; 20; 104] ++ [6]).
        2: apply Permutation_middle. apply Permutation_cons. simpl.
        apply Permutation_trans with (l' := 6 :: [300; 290; 20; 104] ++ []).
        2: apply Permutation_middle. apply Permutation_cons. simpl.
        apply Permutation_trans with (l' := 20 :: [300; 290] ++ [104]).
        2: apply Permutation_middle. apply Permutation_cons. simpl.
        apply Permutation_trans with (l' := 104 :: [300; 290] ++ []).
        2: apply Permutation_middle. apply Permutation_cons. simpl.
        apply Permutation_trans with (l' := 290 :: [300] ++ []).
        2: apply Permutation_middle. apply Permutation_cons. simpl.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat constructor; simpl; try lia.
Qed.