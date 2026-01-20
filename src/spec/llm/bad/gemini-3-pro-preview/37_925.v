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

Example test_sort_even_case : sort_even_spec [5; 3; 2; 5; -3; 3; -11; 0; 123; 0; -10; 3; 3; -9; 3] [-11; 3; -10; 5; -3; 3; 2; 0; 3; 0; 3; 3; 5; -9; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 15 (destruct i; [ try (simpl in Hodd; discriminate); try (simpl; reflexivity) | ]).
      simpl in Hlen; lia.
    + split.
      * simpl.
        eapply Permutation_trans. 2: symmetry; apply Permutation_cons_app with (l1 := [-11; -10; -3; 2; 3; 3]).
        apply Permutation_cons.
        eapply Permutation_trans. 2: symmetry; apply Permutation_cons_app with (l1 := [-11; -10; -3]).
        apply Permutation_cons.
        eapply Permutation_trans. 2: symmetry; apply Permutation_cons_app with (l1 := [-11; -10]).
        apply Permutation_cons.
        apply Permutation_cons.
        eapply Permutation_trans. 2: symmetry; apply Permutation_cons_app with (l1 := [-10; 3; 3]).
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_nil.
      * simpl.
        repeat (apply Sorted_cons; [| apply HdRel_cons; lia || apply HdRel_nil]).
        apply Sorted_nil.
Qed.