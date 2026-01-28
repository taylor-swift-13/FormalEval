Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [6.2] (-201) false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    assert (HIn : In 6.2 [6.2]).
    { simpl. left. reflexivity. }
    apply H in HIn.
    lra.
  - intros H.
    discriminate.
Qed.