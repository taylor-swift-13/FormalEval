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
  [5; -11; 4; 6; -5; 2; -3; 3; -9; 0; 123; 1; -10] 
  [-10; -11; -9; 6; -5; 2; -3; 3; 4; 0; 5; 1; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length *)
    simpl. reflexivity.
  - split.
    + (* Odd indices *)
      intros i Hlen Hodd.
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen; lia.
    + split.
      * (* Permutation *)
        simpl.
        (* 5 *)
        apply Permutation_trans with (l' := 5 :: [-10; -9; -5; -3; 4] ++ [123]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        (* 4 *)
        simpl. apply Permutation_trans with (l' := 4 :: [-10; -9; -5; -3] ++ [123]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        (* -5 *)
        simpl. apply Permutation_trans with (l' := -5 :: [-10; -9] ++ [-3; 123]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        (* -3 *)
        simpl. apply Permutation_trans with (l' := -3 :: [-10; -9] ++ [123]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        (* -9 *)
        simpl. apply Permutation_trans with (l' := -9 :: [-10] ++ [123]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        (* 123 *)
        simpl. apply Permutation_trans with (l' := 123 :: [-10] ++ []).
        2: apply Permutation_middle.
        apply Permutation_cons.
        (* -10 *)
        simpl. apply Permutation_refl.
      * (* Sorted *)
        simpl.
        repeat (constructor; try lia).
Qed.