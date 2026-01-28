Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_57_pre (l: list Z) : Prop := True.

Definition problem_57_spec (l: list Z) (b: bool) : Prop :=
  b = true <-> (Sorted Z.le l \/ Sorted Z.ge l).

Example test_monotonic_2 : problem_57_spec [-5%Z; -7%Z; -9%Z; -9%Z; -11%Z] true.
Proof.
  unfold problem_57_spec.
  split.
  - intros _.
    right.
    apply Sorted_cons.
    + apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_nil.
              ** apply HdRel_nil.
           ++ apply HdRel_cons. lia.
        -- apply HdRel_cons. lia.
      * apply HdRel_cons. lia.
    + apply HdRel_cons. lia.
  - intros _. reflexivity.
Qed.