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
  [1; 1; 1; 2; -12; 0; 1; 1; 1; -5; -5] 
  [-12; 1; -5; 2; 1; 0; 1; 1; 1; -5; 1].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := 1 :: -12 :: 1 :: 1 :: 1 :: -5).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := -12 :: 1 :: 1 :: 1 :: 1 :: -5).
        { apply perm_swap. }
        apply perm_skip.
        apply Permutation_trans with (l' := 1 :: 1 :: 1 :: -5 :: 1).
        { do 3 apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := 1 :: 1 :: -5 :: 1 :: 1).
        { do 2 apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := 1 :: -5 :: 1 :: 1 :: 1).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := -5 :: 1 :: 1 :: 1 :: 1).
        { apply perm_swap. }
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_cons.
                { apply Sorted_cons.
                  { apply Sorted_nil. }
                  { apply HdRel_nil. }
                }
                { apply HdRel_cons. lia. }
              }
              { apply HdRel_cons. lia. }
            }
            { apply HdRel_cons. lia. }
          }
          { apply HdRel_cons. lia. }
        }
        { apply HdRel_cons. lia. }
Qed.