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
  [2; 3; 4; 6; 7; 10; 5; 10; 7; 2; 6; 7; 7] 
  [2; 3; 4; 6; 5; 10; 6; 10; 7; 2; 7; 7; 7].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_count_occ with (eq_dec := Z.eq_dec).
        intro x.
        simpl.
        destruct (Z.eq_dec 2 x); [ subst; reflexivity | ].
        destruct (Z.eq_dec 4 x); [ subst; reflexivity | ].
        destruct (Z.eq_dec 7 x); [ subst; reflexivity | ].
        destruct (Z.eq_dec 5 x); [ subst; reflexivity | ].
        destruct (Z.eq_dec 6 x); [ subst; reflexivity | ].
        reflexivity.
      * simpl.
        repeat (apply Sorted_cons; [ try apply HdRel_cons; try apply HdRel_nil; try lia | ]).
        apply Sorted_nil.
Qed.