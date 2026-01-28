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

Example test_sort_even_case : sort_even_spec [9; -7; 2; 3; 4; 6; 7; 10; 5; 10] [2; -7; 4; 3; 5; 6; 7; 10; 9; 10].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | simpl in Hlen; try lia ]).
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS: [9; 2; 4; 7; 5] *)
        (* RHS: [2; 4; 5; 7; 9] *)
        apply perm_trans with (l' := [2; 9; 4; 7; 5]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_trans with (l' := [4; 9; 7; 5]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_trans with (l' := [7; 9; 5]).
        { apply perm_swap. }
        apply perm_trans with (l' := [7; 5; 9]).
        { apply perm_skip. apply perm_swap. }
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_cons.
                { apply Sorted_nil. }
                { apply HdRel_nil. } }
              { apply HdRel_cons; lia. } }
            { apply HdRel_cons; lia. } }
          { apply HdRel_cons; lia. } }
        { apply HdRel_cons; lia. }
Qed.