Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_34_pre (input : list Z) : Prop := True.

Definition problem_34_spec (input : list Z) (output : list Z) : Prop :=
  Sorted Z.le output /\
  NoDup output /\
  (forall z, In z input <-> In z output).

Example test_problem_34 :
  problem_34_spec [2; 1; 1; 1; 1; 1] [1; 2].
Proof.
  unfold problem_34_spec.
  split.
  {
    repeat apply Sorted_cons.
    - apply Sorted_nil.
    - apply HdRel_nil.
    - apply HdRel_cons; lia.
  }
  split.
  {
    repeat apply NoDup_cons.
    all: try (simpl; intuition; lia).
    apply NoDup_nil.
  }
  {
    intro z.
    split; intro H; simpl in *; intuition.
  }
Qed.