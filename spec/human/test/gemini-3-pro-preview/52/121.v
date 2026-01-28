Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [5.5; 6.2; 7.9; 8.1] 10 true.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    reflexivity.
  - intros _ x HIn.
    simpl in HIn.
    destruct HIn as [H | [H | [H | [H | H]]]].
    + rewrite <- H.
      lra.
    + rewrite <- H.
      lra.
    + rewrite <- H.
      lra.
    + rewrite <- H.
      lra.
    + contradiction.
Qed.