Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [5.5; 6.2212876393256; 6.2; 7.9; 6.2] (-200) false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* We exhibit a counter-example to the universal quantification *)
    assert (HIn : In 5.5 [5.5; 6.2212876393256; 6.2; 7.9; 6.2]).
    { simpl. left. reflexivity. }
    specialize (H 5.5 HIn).
    lra.
  - (* Right to Left implication *)
    intros H.
    discriminate.
Qed.