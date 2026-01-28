Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [30; 97; 90; 59] 0 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* Show that the list contains an element >= 0, contradicting H *)
    assert (H_in : In 30 [30; 97; 90; 59]).
    { simpl. left. reflexivity. }
    apply H in H_in.
    lia.
  - (* Right to Left implication *)
    intros H.
    discriminate H.
Qed.