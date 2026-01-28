Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec 
  [6576799211228067 / 1000000000000000; 
   55/10; 
   15311576847949309 / 10000000000000000; 
   550048632089892 / 100000000000000; 
   62212876393256 / 10000000000000; 
   79/10; 
   79/10] 
  (-199) 
  false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. inversion H.
  - intros H.
    specialize (H (55/10)).
    assert (In (55/10) [6576799211228067 / 1000000000000000; 55 / 10;
        15311576847949309 / 10000000000000000; 550048632089892 / 100000000000000;
        62212876393256 / 10000000000000; 79 / 10; 79 / 10]).
    { simpl. right. left. reflexivity. }
    apply H in H0.
    lra.
Qed.