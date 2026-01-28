Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [1; 3; 4] 2 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* Use a counter-example from the list to derive a contradiction *)
    specialize (H 3).
    assert (HIn : In 3 [1; 3; 4]).
    { simpl. right. left. reflexivity. }
    apply H in HIn.
    lia.
  - (* Right to Left implication *)
    intros H.
    discriminate.
Qed.