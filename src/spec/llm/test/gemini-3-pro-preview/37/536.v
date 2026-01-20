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
  [1; -12; 1; 2; 3; -11; 5; 5; 6; 7; 10; 5; 1] 
  [1; -12; 1; 2; 1; -11; 3; 5; 5; 7; 6; 5; 10].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        do 2 apply perm_skip.
        change [3; 5; 6; 10; 1] with ([3; 5; 6; 10] ++ [1]).
        change [1; 3; 5; 6; 10] with ([1] ++ [3; 5; 6; 10]).
        apply Permutation_app_comm.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| simpl; first [ apply HdRel_nil | apply HdRel_cons; lia ] ]).
        apply Sorted_nil.
Qed.