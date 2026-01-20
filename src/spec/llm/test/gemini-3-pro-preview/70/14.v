Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Inductive strange_interleave : list Z -> list Z -> Prop :=
| si_nil : strange_interleave [] []
| si_one : forall x, strange_interleave [x] [x]
| si_step : forall x y mid res,
    strange_interleave mid res ->
    strange_interleave (x :: mid ++ [y]) (x :: y :: res).

Definition strange_sort_list_spec (lst : list Z) (ans : list Z) : Prop :=
  exists sorted_lst,
    Permutation lst sorted_lst /\
    Sorted Z.le sorted_lst /\
    strange_interleave sorted_lst ans.

Example test_case : strange_sort_list_spec [100; 200; 300; 150; 75; 35; 10] [10; 300; 35; 200; 75; 150; 100].
Proof.
  unfold strange_sort_list_spec.
  exists [10; 35; 75; 100; 150; 200; 300].
  split.
  - apply Permutation_sym.
    transitivity (10 :: [100; 200; 300; 150; 75; 35] ++ []).
    2: apply Permutation_middle.
    constructor. simpl.
    transitivity (35 :: [100; 200; 300; 150; 75] ++ []).
    2: apply Permutation_middle.
    constructor. simpl.
    transitivity (75 :: [100; 200; 300; 150] ++ []).
    2: apply Permutation_middle.
    constructor. simpl.
    transitivity (100 :: [] ++ [200; 300; 150]).
    2: apply Permutation_middle.
    constructor. simpl.
    transitivity (150 :: [200; 300] ++ []).
    2: apply Permutation_middle.
    constructor. simpl.
    transitivity (200 :: [] ++ [300]).
    2: apply Permutation_middle.
    constructor. simpl.
    apply Permutation_refl.
  - split.
    + repeat constructor; try lia.
    + change [10; 35; 75; 100; 150; 200; 300] with (10 :: [35; 75; 100; 150; 200] ++ [300]).
      apply si_step.
      change [35; 75; 100; 150; 200] with (35 :: [75; 100; 150] ++ [200]).
      apply si_step.
      change [75; 100; 150] with (75 :: [100] ++ [150]).
      apply si_step.
      apply si_one.
Qed.