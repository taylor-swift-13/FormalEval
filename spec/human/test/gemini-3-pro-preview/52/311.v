Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [-200; 300; 8000000; -600; 300] 100 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* We need to show a contradiction because false = true is impossible.
       We do this by finding an element in the list >= 100. *)
    specialize (H 300).
    assert (In 300 [-200; 300; 8000000; -600; 300]).
    { simpl. right. left. reflexivity. }
    apply H in H0.
    lia.
  - (* Right to Left implication *)
    intros H.
    discriminate.
Qed.