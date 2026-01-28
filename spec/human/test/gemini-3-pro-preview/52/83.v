Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [4; -4; -2; 7; 10] 6 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* We demonstrate a counter-example: 7 is in the list but not < 6 *)
    assert (7 < 6).
    {
      apply H.
      simpl.
      right; right; right; left.
      reflexivity.
    }
    lia.
  - (* Right to Left implication *)
    intros H.
    discriminate.
Qed.