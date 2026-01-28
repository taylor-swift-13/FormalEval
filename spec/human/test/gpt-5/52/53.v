Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
Import ListNotations.
Open Scope R_scope.

Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [3.5%R; 2.2%R; 1.1%R] (-4)%R false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    specialize (H 3.5%R).
    assert (In 3.5%R [3.5%R; 2.2%R; 1.1%R]) as Hin by (simpl; left; reflexivity).
    specialize (H Hin).
    assert (-4%R < 3.5%R) by lra.
    apply (Rlt_asym 3.5%R (-4)%R) in H.
    contradiction.
  - intros Heq.
    intros x Hin.
    exfalso. discriminate Heq.
Qed.