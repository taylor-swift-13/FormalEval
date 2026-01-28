Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [100; 200; 300; 0.1; 0.2; 0.3; 0.2; 100] 0 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (In 100 [100; 200; 300; 0.1; 0.2; 0.3; 0.2; 100]) as Hin by (simpl; auto).
    apply H in Hin.
    lra.
Qed.