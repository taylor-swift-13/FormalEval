Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => x < t) l) /\
  (res = false <-> exists x, In x l /\ t <= x).

Example test_below_threshold : below_threshold_spec [6.576799211228067%R; 5.5%R; 5.50048632089892%R; 6.2212876393256%R; 7.9%R] 300 true.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros _.
      (* Prove that all elements in the list are < 300 *)
      repeat constructor; lra.
    + intros _.
      reflexivity.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros H.
      (* true = false is impossible *)
      discriminate H.
    + intros [x [HIn HLe]].
      (* Prove that no element in the list is >= 300 *)
      simpl in HIn.
      destruct HIn as [H | [H | [H | [H | [H | H]]]]]; subst; try lra; try contradiction.
Qed.