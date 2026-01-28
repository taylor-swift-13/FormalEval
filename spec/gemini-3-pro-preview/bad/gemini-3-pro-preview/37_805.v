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
  [5; 3; -5; -3; 3; 4; -9; 0; 123; 1; -10] 
  [-10; 3; -9; -3; -5; 4; 3; 0; 5; 1; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        change [-10; -9; -5; 3; 5; 123] with ([-10; -9; -5; 3] ++ 5 :: [123]).
        eapply Permutation_trans. 2: apply Permutation_sym; apply Permutation_middle.
        apply Permutation_cons.
        
        change [-10; -9; -5; 3; 123] with ([-10; -9] ++ -5 :: [3; 123]).
        eapply Permutation_trans. 2: apply Permutation_sym; apply Permutation_middle.
        apply Permutation_cons.

        change [-10; -9; 3; 123] with ([-10; -9] ++ 3 :: [123]).
        eapply Permutation_trans. 2: apply Permutation_sym; apply Permutation_middle.
        apply Permutation_cons.

        change [-10; -9; 123] with ([-10] ++ -9 :: [123]).
        eapply Permutation_trans. 2: apply Permutation_sym; apply Permutation_middle.
        apply Permutation_cons.

        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_cons; try apply HdRel_nil; try lia]).
        apply Sorted_nil.
Qed.