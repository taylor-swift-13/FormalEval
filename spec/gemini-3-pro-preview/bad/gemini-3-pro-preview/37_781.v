Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint get_evens (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: tl => x :: get_evens tl
  end.

Definition sort_even_spec (l res : list Z) : Prop :=
  length l = length res /\
  (forall i : nat, (i < length l)%nat -> Nat.odd i = true -> nth i l 0 = nth i res 0) /\
  Permutation (get_evens l) (get_evens res) /\
  Sorted Z.le (get_evens res).

Example test_sort_even_case : sort_even_spec 
  [5; 3; -5; 2; 5; -3; 3; -11; -9; 0; 123; 0; -10; 3; 3] 
  [-10; 3; -9; 2; -5; -3; 3; -11; 3; 0; 5; 0; 5; 3; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        (* Goal: Permutation [5; -5; 5; 3; -9; 123; -10; 3] [-10; -9; -5; 3; 3; 5; 5; 123] *)
        (* Sort the left list to match the right list step-by-step *)
        apply Permutation_trans with (l' := -10 :: [5; -5; 5; 3; -9; 123; 3]).
        { apply Permutation_sym. apply Permutation_cons_app. simpl. reflexivity. }
        apply Permutation_cons.
        
        apply Permutation_trans with (l' := -9 :: [5; -5; 5; 3; 123; 3]).
        { apply Permutation_sym. apply Permutation_cons_app. simpl. reflexivity. }
        apply Permutation_cons.

        apply Permutation_trans with (l' := -5 :: [5; 5; 3; 123; 3]).
        { apply Permutation_sym. apply Permutation_cons_app. simpl. reflexivity. }
        apply Permutation_cons.

        apply Permutation_trans with (l' := 3 :: [5; 5; 123; 3]).
        { apply Permutation_sym. apply Permutation_cons_app. simpl. reflexivity. }
        apply Permutation_cons.

        apply Permutation_trans with (l' := 3 :: [5; 5; 123]).
        { apply Permutation_sym. apply Permutation_cons_app. simpl. reflexivity. }
        apply Permutation_cons.

        (* Remaining lists [5; 5; 123] match *)
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| try apply HdRel_cons; try apply HdRel_nil; lia]).
        apply Sorted_nil.
Qed.