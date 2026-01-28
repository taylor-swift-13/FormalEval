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
  [1; 2; 3; -7; 5; 1; 0; -8; 9; -12; 7; 6; 6; 1] 
  [-12; 2; 3; -7; 5; 1; 0; -8; 9; 1; 7; 6; 6; 1].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* We check indices 0 to 13 individually. Indices divisible by 3 use H to solve. *)
      do 14 (destruct i; [ simpl; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      (* Indices >= 14 are out of bounds for both lists *)
      simpl. reflexivity.
    + split.
      * simpl.
        (* Goal: Permutation [-12; -7; 0; 1; 6] [1; -7; 0; -12; 6] *)
        transitivity (1 :: [-12; -7; 0; 6]).
        { apply Permutation_sym.
          change (-12 :: -7 :: 0 :: 1 :: 6 :: []) with ((-12 :: -7 :: 0 :: []) ++ 1 :: 6 :: []).
          apply Permutation_middle. }
        { apply Permutation_cons.
          (* Goal: Permutation [-12; -7; 0; 6] [-7; 0; -12; 6] *)
          transitivity (-7 :: -12 :: 0 :: 6 :: []).
          - apply Permutation_swap.
          - apply Permutation_cons.
            (* Goal: Permutation [-12; 0; 6] [0; -12; 6] *)
            apply Permutation_swap. }
      * simpl.
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_cons.
                { apply Sorted_nil. }
                { apply HdRel_nil. } }
              { apply HdRel_cons. apply Z.leb_le. reflexivity. } }
            { apply HdRel_cons. apply Z.leb_le. reflexivity. } }
          { apply HdRel_cons. apply Z.leb_le. reflexivity. } }
        { apply HdRel_cons. apply Z.leb_le. reflexivity. }
Qed.