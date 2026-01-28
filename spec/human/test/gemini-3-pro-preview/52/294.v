Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [100; 9999999; -400] 8000001 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* We demonstrate a contradiction by finding an element >= threshold *)
    specialize (H 9999999).
    assert (In 9999999 [100; 9999999; -400]).
    { simpl. right. left. reflexivity. }
    apply H in H0.
    lia.
  - (* Right to Left implication *)
    intros H.
    discriminate H.
Qed.