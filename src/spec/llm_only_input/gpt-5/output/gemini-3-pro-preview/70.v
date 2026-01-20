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

Example test_case :
  strange_sort_list_spec [1%Z; 2%Z; 3%Z; 4%Z] [1%Z; 4%Z; 2%Z; 3%Z].
Proof.
  unfold strange_sort_list_spec.
  exists [1%Z; 2%Z; 3%Z; 4%Z].
  split.
  - apply Permutation_refl.
  - split.
    + repeat constructor.
      * lia.
      * lia.
      * lia.
    + assert (H23 : strange_interleave [2%Z; 3%Z] [2%Z; 3%Z]).
      { apply (si_step 2%Z 3%Z [] []); apply si_nil. }
      apply (si_step 1%Z 4%Z [2%Z; 3%Z] [2%Z; 3%Z]); exact H23.
Qed.