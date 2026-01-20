Existing Coq output file content for the new test case:
```coq
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
  [4; -2; -12; -9; 23; 2; 3; 11; 13; -10; 13; 4; -13; -12; 4] 
  [-13; -2; -12; -9; 3; 2; 4; 11; 4; -10; 13; 4; 13; -12; 23].
Proof.
  unfold sort_even_spec.
  split.
  { simpl. reflexivity. }
  split.
  {
    intros i Hlen Hodd.
    repeat (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
    simpl in Hlen. lia.
  }
  split.
  {
    simpl.
    transitivity (4 :: [-13; -12; 3] ++ [4; 13; 13; 23]).
    2: apply Permutation_middle.
    apply Permutation_cons.
    transitivity (-12 :: [-13] ++ [3; 4; 13; 13; 23]).
    2: apply Permutation_middle.
    apply Permutation_cons.
    transitivity (23 :: [-13; 3; 4; 13; 13] ++ []).
    2: apply Permutation_middle.
    apply Permutation_cons.
    rewrite app_nil_r.
    transitivity (3 :: [-13] ++ [4; 13; 13]).
    2: apply Permutation_middle.
    apply Permutation_cons.
    transitivity (13 :: [-13; 4] ++ [13]).
    2: apply Permutation_middle.
    apply Permutation_cons.
    transitivity (13 :: [-13; 4] ++ []).
    2: apply Permutation_middle.
    apply Permutation_cons.
    rewrite app_nil_r.
    apply Permutation_refl.
  }
  {
    simpl.
    repeat (apply Sorted_cons; [| simpl; try apply HdRel_cons; try apply HdRel_nil; lia]).
    apply Sorted_nil.
  }
Qed.