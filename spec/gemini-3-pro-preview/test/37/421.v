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
  [2; 2; 3; 123; 6; 7; 8; 2; 2; 7] 
  [2; 2; 2; 123; 3; 7; 6; 2; 8; 7].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 10 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply perm_skip.
        apply perm_trans with (l' := [3; 6; 2; 8]).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        apply perm_trans with (l' := [3; 2; 6; 8]).
        { apply perm_skip. apply perm_swap. }
        apply perm_swap.
      * simpl.
        apply Sorted_cons.
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
Qed.