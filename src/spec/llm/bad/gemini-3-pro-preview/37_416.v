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

Example test_sort_even_case : sort_even_spec [4; -2; -12; 4; 23; 2; 3; 11; 12; 4; -12] [-12; -2; -12; 4; 3; 2; 4; 11; 12; 4; 23].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We destruct i enough times to cover the list length (11) *)
      do 11 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* If i is larger than the list *)
      simpl in Hlen; lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [4; -12; 23; 3; 12; -12] [-12; -12; 3; 4; 12; 23] *)
        (* Apply Permutation_cons_app to peel off 4 *)
        apply Permutation_cons_app with (l1 := [-12; -12; 3]) (l2 := [12; 23]).
        simpl.
        (* Goal: Permutation [-12; 23; 3; 12; -12] [-12; -12; 3; 12; 23] *)
        (* Heads match *)
        apply Permutation_cons.
        (* Goal: Permutation [23; 3; 12; -12] [-12; 3; 12; 23] *)
        (* Peel off 23 *)
        apply Permutation_cons_app with (l1 := [-12; 3; 12]) (l2 := []).
        simpl.
        (* Goal: Permutation [3; 12; -12] [-12; 3; 12] *)
        (* Peel off 3 *)
        apply Permutation_cons_app with (l1 := [-12]) (l2 := [12]).
        simpl.
        (* Goal: Permutation [12; -12] [-12; 12] *)
        (* Peel off 12 *)
        apply Permutation_cons_app with (l1 := [-12]) (l2 := []).
        simpl.
        (* Goal: Permutation [-12] [-12] *)
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (constructor; try lia).
Qed.