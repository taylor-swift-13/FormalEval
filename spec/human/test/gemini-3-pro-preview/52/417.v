Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [6.576799211228067; 5.5; 1.5311576847949309; 5.50048632089892; 6.2212876393256; 7.9; 7.9] (-199) false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    specialize (H 6.576799211228067).
    assert (In 6.576799211228067 [6.576799211228067; 5.5; 1.5311576847949309; 5.50048632089892; 6.2212876393256; 7.9; 7.9]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lra.
  - (* Right to Left implication *)
    intros H.
    discriminate.
Qed.