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
  [10; 8; 7; 7; 5; 4; 3; 2; 1; 899; 0; -1; -2; -4; -6; -7; -8; -9; -10; -4]
  [-10; 8; 7; -7; 5; 4; -2; 2; 1; 3; 0; -1; 7; -4; -6; 10; -8; -9; 899; -4].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 20 (destruct i as [|i]; [ simpl in H; try congruence; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        apply Permutation_trans with (l' := [-10; -7; -2; 899; 3; 7; 10]).
        -- repeat apply Permutation_cons.
           apply Permutation_sym.
           apply Permutation_middle with (l1 := [3; 7; 10]).
        -- apply Permutation_sym.
           apply Permutation_rev.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.