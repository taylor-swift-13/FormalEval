Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [1; 4; -4; 7; 10] 6 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication: (forall x, In x l -> x < t) -> false = true *)
    intros H.
    (* We must show that the premise leads to a contradiction because output is false. *)
    (* We find an element in the list that is not less than the threshold. *)
    (* 7 is in the list and 7 < 6 is false. *)
    assert (7 < 6).
    {
      apply H.
      simpl.
      right; right; right; left.
      reflexivity.
    }
    lia.
  - (* Right to Left implication: false = true -> ... *)
    intros H.
    discriminate.
Qed.