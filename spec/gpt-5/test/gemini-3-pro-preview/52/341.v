Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => x < t) l) /\
  (res = false <-> exists x, In x l /\ t <= x).

Example test_below_threshold : below_threshold_spec [100; 200; 300; 1/10; 2/10; 3/10; 2/10; 100] 0 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H. discriminate.
    + intros H.
      (* Contradiction: 100 < 0 is false *)
      rewrite Forall_forall in H.
      assert (In 100 [100; 200; 300; 1/10; 2/10; 3/10; 2/10; 100]).
      { left. reflexivity. }
      apply H in H0.
      lra.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      exists 100.
      split.
      * left. reflexivity.
      * lra.
    + intros _. reflexivity.
Qed.