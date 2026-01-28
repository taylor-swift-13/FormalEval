Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition problem_34_pre (input : list R) : Prop := True.

Definition problem_34_spec (input : list R) (output : list R) : Prop :=
  Sorted Rle output /\
  NoDup output /\
  (forall z, In z input <-> In z output).

Example test_problem_34 :
  problem_34_spec [1.1; 3.187467502157803; 3.3; 4.4; 4.4] [1.1; 3.187467502157803; 3.3; 4.4].
Proof.
  unfold problem_34_spec.
  split.
  {
    repeat apply Sorted_cons.
    - apply Sorted_nil.
    - apply HdRel_nil.
    - apply HdRel_cons; lra.
    - apply HdRel_cons; lra.
    - apply HdRel_cons; lra.
  }
  split.
  {
    repeat apply NoDup_cons.
    all: try (simpl; intuition; lra).
    apply NoDup_nil.
  }
  {
    intro z.
    split; intro H; simpl in *; intuition.
  }
Qed.