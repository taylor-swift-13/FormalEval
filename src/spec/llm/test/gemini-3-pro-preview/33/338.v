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

Example test_case : sort_third_spec [9; -5; 0; -1; 6; 19; -5; 3; 12; 0] [-5; -5; 0; -1; 6; 19; 0; 3; 12; 9].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for i from 0 to 9, and >9. For indices where i mod 3 = 0, H is contradictory. *)
      do 10 (destruct i; [ simpl in *; try reflexivity; try contradiction | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-5; -1; 0; 9] [9; -1; -5; 0] *)
        (* Peel -5 *)
        change [9; -1; -5; 0] with ([9; -1] ++ -5 :: [0]).
        apply Permutation_cons_app.
        (* Peel -1 *)
        simpl.
        change [9; -1; 0] with ([9] ++ -1 :: [0]).
        apply Permutation_cons_app.
        (* Peel 0 *)
        simpl.
        change [9; 0] with ([9] ++ 0 :: []).
        apply Permutation_cons_app.
        (* Peel 9 *)
        simpl.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Extracted thirds from res: [-5; -1; 0; 9] *)
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; unfold Z.le; simpl; discriminate) ]).
        apply Sorted_nil.
Qed.