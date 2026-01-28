Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [1; 2; 3; -1; 4] 4 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* We need to show that the hypothesis leads to a contradiction because 4 is in the list but not < 4 *)
    specialize (H 4).
    assert (In 4 [1; 2; 3; -1; 4]).
    { simpl. right. right. right. right. left. reflexivity. }
    apply H in H0.
    lia.
  - (* Right to Left implication *)
    intros H.
    discriminate H.
Qed.