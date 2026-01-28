Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [4; -4; 7; 10] 7 false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    (* The hypothesis H claims all elements are < 7. We show a counterexample. *)
    specialize (H 7).
    assert (In 7 [4; -4; 7; 10]) as Hin.
    { simpl. right. right. left. reflexivity. }
    apply H in Hin.
    lia.
  - intros H.
    discriminate.
Qed.