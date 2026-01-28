Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_57_pre (l: list Z) : Prop := True.

Definition problem_57_spec (l: list Z) (b: bool) : Prop :=
  b = true <-> (Sorted Z.le l \/ Sorted Z.ge l).

Example test_monotonic_2 : problem_57_spec [5%Z; 1%Z; -7%Z; -9%Z; 1%Z; 5%Z; 5%Z] false.
Proof.
  unfold problem_57_spec.
  split.
  - intros H. discriminate.
  - intros [H | H].
    + inversion H. subst. inversion H3. subst. lia.
    + inversion H. subst. inversion H3. subst. inversion H5. subst. inversion H7. subst. inversion H9. subst. lia.
Qed.