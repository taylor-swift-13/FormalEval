Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [-5; -4; -3] (-6) false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* Logic: Show that the condition holds for an element that violates the threshold *)
    assert (In (-5) [-5; -4; -3]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lia.
  - (* Right to Left implication *)
    intros H.
    discriminate H.
Qed.