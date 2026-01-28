Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_57_pre (l: list Z) : Prop := True.

Definition problem_57_spec (l: list Z) (b: bool) : Prop :=
  b = true <-> (Sorted Z.le l \/ Sorted Z.ge l).

Example test_monotonic_2 : problem_57_spec [1%Z; 1%Z; 2%Z; 3%Z; 3%Z; 3%Z; 4%Z; 5%Z] true.
Proof.
  unfold problem_57_spec.
  split.
  - intros _.
    left.
    apply Sorted_cons.
    + apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_cons.
                 --- apply Sorted_cons.
                     +++ apply Sorted_cons.
                         *** apply Sorted_nil.
                         *** apply HdRel_nil.
                     +++ apply HdRel_cons. lia.
                 --- apply HdRel_cons. lia.
              ** apply HdRel_cons. lia.
           ++ apply HdRel_cons. lia.
        -- apply HdRel_cons. lia.
      * apply HdRel_cons. lia.
    + apply HdRel_cons. lia.
  - intros _. reflexivity.
Qed.