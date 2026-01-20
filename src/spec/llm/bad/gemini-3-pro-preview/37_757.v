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

Example test_sort_even_case : sort_even_spec [5; 5; 4; 4; 0; 5; 0; 5] [0; 5; 0; 4; 4; 5; 5; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 8 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        transitivity ([4; 0; 0] ++ [5]).
        { apply Permutation_middle. }
        apply Permutation_app_tail.
        transitivity ([0; 0] ++ [4]).
        { apply Permutation_middle. }
        simpl. apply Permutation_refl.
      * simpl.
        apply Sorted_cons; [| apply HdRel_cons; lia].
        apply Sorted_cons; [| apply HdRel_cons; lia].
        apply Sorted_cons; [| apply HdRel_cons; lia].
        apply Sorted_cons; [ apply Sorted_nil | apply HdRel_nil ].
Qed.