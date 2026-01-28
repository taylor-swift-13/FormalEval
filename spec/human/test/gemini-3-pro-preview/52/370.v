Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [100; 200; 300; 0.1; 0.2; 0.3; 0.2; 100] 9 false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    assert (HIn : In 100 [100; 200; 300; 0.1; 0.2; 0.3; 0.2; 100]).
    { simpl. left. reflexivity. }
    specialize (H 100 HIn).
    lra.
  - intros H.
    discriminate.
Qed.