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
  [9; 0; 3; -3; -4; 0; 9; -5; 3; -4; 3] 
  [-4; 0; 3; -3; -4; 0; 9; -5; 3; 9; 3].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Exhaustively check indices 0 to 10; for i > 10 both are None *)
      do 12 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-4; -3; 9; 9] [9; -3; 9; -4] *)
        transitivity (-4 :: [9; -3; 9]).
        { (* Left side: Permutation [-4; -3; 9; 9] (-4 :: [9; -3; 9]) *)
          apply perm_skip. 
          (* Permutation [-3; 9; 9] [9; -3; 9] -> swap first two *)
          apply perm_swap. }
        { (* Right side: Permutation (-4 :: [9; -3; 9]) [9; -3; 9; -4] *)
          change (9 :: -3 :: 9 :: -4 :: []) with ([9; -3; 9] ++ [-4]).
          apply Permutation_middle. }
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Goal: Sorted Z.le [-4; -3; 9; 9] *)
        repeat (apply Sorted_cons; [ | apply HdRel_nil || (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.