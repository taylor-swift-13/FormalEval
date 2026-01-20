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

Example test_sort_even_case : sort_even_spec [1; 1; -4; 0; 2; 2; 2; 2; -5; 2] [-5; 1; -4; 0; 1; 2; 2; 2; 2; 2].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length check *)
    simpl. reflexivity.
  - split.
    + (* Odd indices check *)
      intros i Hi Hodd.
      do 10 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hi. lia.
    + split.
      * (* Permutation check *)
        simpl.
        apply Permutation_cons_app with (l1 := [-5; -4]) (l2 := [2; 2]).
        simpl.
        apply Permutation_cons_app with (l1 := [-5]) (l2 := [2; 2]).
        simpl.
        apply Permutation_cons_app with (l1 := [-5]) (l2 := [2]).
        simpl.
        apply Permutation_cons_app with (l1 := [-5]) (l2 := []).
        simpl.
        apply Permutation_refl.
      * (* Sorted check *)
        simpl.
        repeat (constructor; try lia).
Qed.