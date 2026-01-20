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
  [-5; 1; 2; -3; 5; 1; 289; 16; 16; -8; 9; -12; 7; 6; -12; 16; 1; 5; 5]
  [-8; 1; 2; -5; 5; 1; -3; 16; 16; 5; 9; -12; 7; 6; -12; 16; 1; 5; 289].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length *)
    simpl. reflexivity.
  - split.
    + (* 2. Indices *)
      intros i H.
      (* Destruct i enough times to cover the list length (19) *)
      do 19 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      (* Case i >= 19 *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation *)
        simpl.
        (* LHS: [-8; -5; -3; 5; 7; 16; 289] *)
        (* RHS: [-5; -3; 289; -8; 7; 16; 5] *)
        transitivity (-8 :: [-5; -3; 289; 7; 16; 5]).
        { constructor.
          constructor.
          constructor.
          transitivity (5 :: [289; 7; 16]).
          { constructor.
            transitivity (7 :: [289; 16]).
            { constructor. apply Permutation_swap. }
            { apply Permutation_sym. 
              change ([289; 7; 16]) with ([289] ++ 7 :: [16]).
              apply Permutation_middle. }
          }
          { apply Permutation_sym.
            change ([289; 7; 16; 5]) with ([289; 7; 16] ++ 5 :: []).
            apply Permutation_middle. }
        }
        { apply Permutation_sym.
          change ([-5; -3; 289; -8; 7; 16; 5]) with ([-5; -3; 289] ++ -8 :: [7; 16; 5]).
          apply Permutation_middle. }
      * (* 4. Sorted *)
        simpl.
        repeat apply Sorted_cons; try apply Sorted_nil; try apply HdRel_nil; try (apply HdRel_cons; simpl; lia).
Qed.