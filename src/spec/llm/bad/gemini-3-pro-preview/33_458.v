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
  [1; 2; 3; 5; 1; 0; -8; 9; 200; -12; 7; 6; 6; 1; -13; 9; 6] 
  [-12; 2; 3; -8; 1; 0; 1; 9; 200; 5; 7; 6; 6; 1; -13; 9; 6].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i 17 times to cover all indices of the list. *)
      do 17 (destruct i; [
        simpl; 
        match goal with
        | [ H : ?x mod 3 <> 0 |- _ ] => 
            try (exfalso; compute in H; congruence); (* If index is divisible by 3, H is False *)
            reflexivity (* If index is not divisible by 3, values match *)
        end
      | ]).
      (* For i >= 17, both nth_error return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* We use Permutation_middle to reorder elements one by one *)
        change [1; 5; -8; -12; 6; 9] with ([1; 5; -8] ++ -12 :: [6; 9]).
        apply (Permutation_trans _ (-12 :: [1; 5; -8] ++ [6; 9])); [ | apply Permutation_middle ].
        apply Permutation_cons.
        change ([1; 5; -8] ++ [6; 9]) with ([1; 5] ++ -8 :: [6; 9]).
        apply (Permutation_trans _ (-8 :: [1; 5] ++ [6; 9])); [ | apply Permutation_middle ].
        apply Permutation_cons.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; auto ]).
        apply Sorted_nil.
Qed.