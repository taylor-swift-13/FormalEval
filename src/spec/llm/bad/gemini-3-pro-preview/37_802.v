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
  [1; 1; -10; 2; 1; 0; 0; -12; 1; 1; 1; 1] 
  [-10; 1; 0; 2; 1; 0; 1; -12; 1; 1; 1; 1].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length check *)
    simpl. reflexivity.
  - split.
    + (* Odd indices check *)
      intros i Hlen Hodd.
      do 12 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* Permutation check *)
        simpl.
        apply Permutation_trans with (l' := [-10; 1; 1; 0; 1; 1]).
        { apply Permutation_swap. }
        apply Permutation_cons.
        apply Permutation_trans with (l' := [1; 0; 1; 1; 1]).
        { apply Permutation_cons. apply Permutation_swap. }
        apply Permutation_swap.
      * (* Sorted check *)
        simpl.
        repeat constructor; lia.
Qed.