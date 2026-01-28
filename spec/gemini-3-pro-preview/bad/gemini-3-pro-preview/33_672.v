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
  [300; 500; 6; 7; -901; 8; 289; -105; -277; 11; 200; 3; 4; 5; 700; 900; -901; 800; 1000]
  [4; 500; 6; 7; -901; 8; 11; -105; -277; 289; 200; 3; 300; 5; 700; 900; -901; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i enough times to cover the list length (19 elements) and the out-of-bounds case *)
      do 20 (destruct i as [|i]; simpl in *; [ try (exfalso; apply H; reflexivity); try reflexivity | ]).
      reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Strategy: Repeatedly pick the head of LHS, find it in RHS using Permutation_Add, and remove it *)
        repeat (match goal with
        | |- Permutation [] [] => apply Permutation_nil
        | |- Permutation (?x :: ?xs) ?ys =>
             eapply Permutation_trans; 
             [ | apply Permutation_Add; repeat constructor ];
             apply Permutation_cons
        end).
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; constructor; simpl; try discriminate ]).
        apply Sorted_nil.
Qed.