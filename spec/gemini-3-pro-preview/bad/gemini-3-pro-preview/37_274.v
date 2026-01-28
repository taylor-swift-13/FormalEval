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

Example test_sort_even_case : sort_even_spec [4; -2; -12; -9; 23; 2; 3; 11; 12; -10; 4; -12] [-12; -2; 3; -9; 4; 2; 4; 11; 12; -10; 23; -12].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length check *)
    simpl. reflexivity.
  - split.
    + (* Odd indices check *)
      intros i Hlen Hodd.
      destruct i; [ simpl in Hodd; discriminate Hodd | ].
      destruct i; [ simpl; reflexivity | ].
      destruct i; [ simpl in Hodd; discriminate Hodd | ].
      destruct i; [ simpl; reflexivity | ].
      destruct i; [ simpl in Hodd; discriminate Hodd | ].
      destruct i; [ simpl; reflexivity | ].
      destruct i; [ simpl in Hodd; discriminate Hodd | ].
      destruct i; [ simpl; reflexivity | ].
      destruct i; [ simpl in Hodd; discriminate Hodd | ].
      destruct i; [ simpl; reflexivity | ].
      destruct i; [ simpl in Hodd; discriminate Hodd | ].
      destruct i; [ simpl; reflexivity | ].
      simpl in Hlen. lia.
    + split.
      * (* Permutation check *)
        simpl.
        (* Goal: Permutation [4; -12; 23; 3; 12; 4] [-12; 3; 4; 4; 12; 23] *)
        apply Permutation_trans with (-12 :: [4; 23; 3; 12; 4]).
        { change [4; -12; 23; 3; 12; 4] with ([4] ++ -12 :: [23; 3; 12; 4]).
          apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (3 :: [4; 23; 12; 4]).
        { change [4; 23; 3; 12; 4] with ([4; 23] ++ 3 :: [12; 4]).
          apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        apply perm_skip. (* 4 matches 4 *)
        apply Permutation_trans with (4 :: [23; 12]).
        { apply Permutation_sym. apply Permutation_cons_append. }
        apply perm_skip.
        apply perm_swap.
      * (* Sorted check *)
        simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_nil || (apply HdRel_cons; simpl; lia)).
Qed.