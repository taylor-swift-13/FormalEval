Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => x < IZR t) l) /\
  (res = false <-> exists x, In x l /\ IZR t <= x).

Example test_below_threshold : below_threshold_spec [6.576799211228067; 5.5; 1.5311576847949309; 5.50048632089892; 6.2212876393256; 7.9; 7.9] (-199)%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H.
      discriminate H.
    + intros H.
      assert (HIn : In 6.576799211228067 [6.576799211228067; 5.5; 1.5311576847949309; 5.50048632089892; 6.2212876393256; 7.9; 7.9]).
      { simpl. left. reflexivity. }
      rewrite Forall_forall in H.
      specialize (H _ HIn).
      lra.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      exists 6.576799211228067.
      split.
      * simpl. left. reflexivity.
      * lra.
    + intros _.
      reflexivity.
Qed.