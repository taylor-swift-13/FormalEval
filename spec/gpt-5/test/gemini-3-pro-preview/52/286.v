Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => x < t) l) /\
  (res = false <-> exists x, In x l /\ t <= x).

Example test_below_threshold : below_threshold_spec [5.5; 6.2; 7.934953681964755; 8.1; 5.6573184258702085; 6.2] 10 true.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros _.
      repeat constructor; lra.
    + intros _.
      reflexivity.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros H.
      discriminate H.
    + intros [x [HIn HLe]].
      simpl in HIn.
      destruct HIn as [H | [H | [H | [H | [H | [H | H]]]]]]; subst; lra.
Qed.