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
  [300; 500; 6; -10; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; -278; 700; 900; -901; 800; 1000; -105] 
  [-10; 500; 6; 4; 8; 289; 20; -105; -277; 104; 200; 3; 300; 5; -278; 700; 900; -901; 800; 1000; -105].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i; [ simpl in *; try (exfalso; apply H; reflexivity); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply perm_trans with (-10 :: 300 :: 20 :: 104 :: 4 :: 700 :: 800 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_trans with (300 :: 20 :: 4 :: 104 :: 700 :: 800 :: []).
        { do 2 apply perm_skip. apply perm_swap. }
        apply perm_trans with (300 :: 4 :: 20 :: 104 :: 700 :: 800 :: []).
        { apply perm_skip. apply perm_swap. }
        apply perm_trans with (4 :: 300 :: 20 :: 104 :: 700 :: 800 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_trans with (20 :: 300 :: 104 :: 700 :: 800 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_trans with (104 :: 300 :: 700 :: 800 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | first [ apply HdRel_nil | apply HdRel_cons; compute; try (intro Hcontra; discriminate) ] ]).
        apply Sorted_nil.
Qed.