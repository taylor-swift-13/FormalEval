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

Example test_sort_even_case : sort_even_spec [5; 0; 5; 0; 5; -12; 0; 5] [0; 0; 5; 0; 5; -12; 5; 5].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length check *)
    simpl. reflexivity.
  - split.
    + (* Odd indices check *)
      intros i Hlen Hodd.
      do 8 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* Permutation check *)
        simpl.
        apply Permutation_sym.
        change [5; 5; 5; 0] with ([5; 5; 5] ++ [0]).
        apply Permutation_middle with (l1 := [5; 5; 5]).
      * (* Sorted check *)
        simpl.
        repeat (constructor; try lia).
Qed.