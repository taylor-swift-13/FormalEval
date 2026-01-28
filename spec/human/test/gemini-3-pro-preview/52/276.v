Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [10; 20; -30; 40; -50; -50] 12 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* The hypothesis implies all elements are < 12, but 20 is in the list *)
    specialize (H 20).
    assert (In 20 [10; 20; -30; 40; -50; -50]) as HIn.
    { simpl. right. left. reflexivity. }
    apply H in HIn.
    (* Contradiction: 20 < 12 is false *)
    lia.
  - (* Right to Left implication *)
    intros H.
    (* false = true is a contradiction *)
    discriminate H.
Qed.