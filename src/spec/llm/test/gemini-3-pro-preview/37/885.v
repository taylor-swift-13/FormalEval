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

Example test_sort_even_case : sort_even_spec [0; -7; 5; -1; 5; 5; 0] [0; -7; 0; -1; 5; 5; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 7 (destruct i as [|i]; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply perm_skip.
        apply Permutation_sym.
        apply Permutation_cons_app with (l1 := [5; 5]) (l2 := []).
        simpl. reflexivity.
      * simpl.
        repeat apply Sorted_cons; try apply HdRel_cons; try apply Sorted_nil; try apply HdRel_nil; try lia.
Qed.