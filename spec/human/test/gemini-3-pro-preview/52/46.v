Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [-1; -2; -4] (-4) false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* The hypothesis H implies that every element in the list is less than -4.
       We show a contradiction by picking -1, which is in the list but not < -4. *)
    specialize (H (-1)).
    assert (In (-1) [-1; -2; -4]) as HIn.
    { simpl. left. reflexivity. }
    apply H in HIn.
    lia.
  - (* Right to Left implication *)
    intros H.
    (* false = true is a contradiction *)
    discriminate H.
Qed.