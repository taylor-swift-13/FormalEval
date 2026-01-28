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

Example test_sort_even_case : sort_even_spec [4; 3; 2; 5; 2; 2; 1; 1; 1] [1; 3; 1; 5; 2; 2; 2; 1; 4].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 10 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_sym.
        etransitivity.
        2: apply Permutation_middle with (l1 := [4; 2; 2]) (l2 := [1]).
        constructor.
        etransitivity.
        2: apply Permutation_middle with (l1 := [4; 2; 2]) (l2 := []).
        constructor.
        etransitivity.
        2: apply Permutation_middle with (l1 := [4]) (l2 := [2]).
        constructor.
        etransitivity.
        2: apply Permutation_middle with (l1 := [4]) (l2 := []).
        constructor.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| try apply HdRel_nil; try (apply HdRel_cons; lia)]).
        apply Sorted_nil.
Qed.