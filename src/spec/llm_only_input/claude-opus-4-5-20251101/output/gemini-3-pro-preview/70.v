Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
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

Example test_strange_sort :
  strange_sort_list_spec [1%Z; 2%Z; 3%Z; 4%Z] [1%Z; 4%Z; 2%Z; 3%Z].
Proof.
  unfold strange_sort_list_spec.
  exists [1%Z; 2%Z; 3%Z; 4%Z].
  split.
  - (* Permutation [1; 2; 3; 4] [1; 2; 3; 4] *)
    reflexivity.
  - split.
    + (* Sorted Z.le [1; 2; 3; 4] *)
      repeat constructor; lia.
    + (* strange_interleave [1; 2; 3; 4] [1; 4; 2; 3] *)
      (* [1; 2; 3; 4] = 1 :: [2; 3] ++ [4] *)
      (* We need strange_interleave [2; 3] [2; 3] *)
      (* [2; 3] = 2 :: [] ++ [3] *)
      (* We need strange_interleave [] [] *)
      assert (H1: [1; 2; 3; 4] = 1 :: [2; 3] ++ [4]).
      { simpl. reflexivity. }
      rewrite H1.
      apply si_step.
      assert (H2: [2; 3] = 2 :: [] ++ [3]).
      { simpl. reflexivity. }
      rewrite H2.
      apply si_step.
      apply si_nil.
Qed.