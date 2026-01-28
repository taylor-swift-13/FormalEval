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
  [-7; 3; 4; 3; 5; 7; 7; 10; 2; 4; 4; 3] 
  [-7; 3; 2; 3; 4; 7; 4; 10; 5; 4; 7; 3].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 12 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_skip.
        apply Permutation_trans with (l' := 4 :: 2 :: 4 :: 5 :: 7).
        { apply Permutation_skip.
          apply Permutation_trans with (l' := 5 :: 2 :: 4 :: 7).
          { apply Permutation_skip.
            apply Permutation_trans with (l' := 7 :: 2 :: 4).
            { apply Permutation_skip. apply Permutation_refl. }
            apply Permutation_trans with (l' := 2 :: 7 :: 4).
            { apply Permutation_swap. }
            apply Permutation_skip. apply Permutation_swap.
          }
          apply Permutation_trans with (l' := 2 :: 5 :: 4 :: 7).
          { apply Permutation_swap. }
          apply Permutation_skip. apply Permutation_swap.
        }
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_cons; try lia ]).
        apply Sorted_nil.
Qed.