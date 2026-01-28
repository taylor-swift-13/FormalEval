Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => x < t) l) /\
  (res = false <-> exists x, In x l /\ t <= x).

Example test_below_threshold : below_threshold_spec [100; 200; 300; 0.1; 0.2; 0.3; 0.2] 40 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H.
      (* false = true is impossible *)
      discriminate H.
    + intros H.
      (* Prove contradiction: 100 is in the list but 100 >= 40 *)
      assert (In 100 [100; 200; 300; 0.1; 0.2; 0.3; 0.2]) as HIn.
      { simpl. left. reflexivity. }
      rewrite Forall_forall in H.
      specialize (H _ HIn).
      lra.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      exists 100.
      split.
      * simpl. left. reflexivity.
      * lra.
    + intros _.
      reflexivity.
Qed.