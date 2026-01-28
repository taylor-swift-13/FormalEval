Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => x < t) l) /\
  (res = false <-> exists x, In x l /\ t <= x).

Example test_below_threshold : below_threshold_spec [6.576799211228067; 5.5; 5.50048632089892; 6.2212876393256; 7.9; 7.9] 300 true.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros _.
      repeat constructor; lra.
    + intros _.
      reflexivity.
  - split.
    + intros H.
      discriminate H.
    + intros [x [HIn HLe]].
      simpl in HIn.
      destruct HIn as [H | [H | [H | [H | [H | [H | H]]]]]]; subst; lra.
Qed.