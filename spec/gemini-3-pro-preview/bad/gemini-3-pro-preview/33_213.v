Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Example test_case : sort_third_spec 
  [5%Z; 2%Z; 7%Z; 9%Z; 3%Z; -7%Z; 11%Z; 8%Z; 0%Z; 1%Z; -1%Z; 13%Z; 11%Z; 6%Z; -2%Z; 104%Z; 13%Z] 
  [1%Z; 2%Z; 7%Z; 5%Z; 3%Z; -7%Z; 9%Z; 8%Z; 0%Z; 11%Z; -1%Z; 13%Z; 11%Z; 6%Z; -2%Z; 104%Z; 13%Z].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Handle indices 0 to 16 explicitly to avoid timeout on symbolic evaluation *)
      do 17 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      (* For i >= 17, both lists are exhausted *)
      simpl. reflexivity.
    + split.
      * simpl.
        (* Prove Permutation [1; 5; 9; 11; 11; 104] [5; 9; 11; 1; 11; 104] *)
        change [5; 9; 11; 1; 11; 104] with ([5; 9; 11] ++ 1 :: [11; 104]).
        apply Permutation_middle.
      * simpl.
        repeat constructor.
        all: try (apply Z.leb_le; reflexivity).
Qed.