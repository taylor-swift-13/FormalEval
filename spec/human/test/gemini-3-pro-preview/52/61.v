Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [-1; -2; -4] (-5) false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* We need to show that the hypothesis leads to a contradiction because false = true is impossible. *)
    (* Specifically, -1 is in the list but not less than -5. *)
    assert (HIn : In (-1) [-1; -2; -4]).
    { simpl. left. reflexivity. }
    apply H in HIn.
    lia.
  - (* Right to Left implication *)
    intros H.
    (* Hypothesis H is false = true, which is a contradiction. *)
    discriminate H.
Qed.