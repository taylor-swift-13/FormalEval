Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [9; 20; 2000; 40; -50] 499 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* Instantiate the hypothesis with the counterexample 2000 *)
    specialize (H 2000).
    (* Prove that 2000 is in the list *)
    assert (In 2000 [9; 20; 2000; 40; -50]).
    { simpl. right. right. left. reflexivity. }
    apply H in H0.
    (* Contradiction: 2000 < 499 is false *)
    lia.
  - (* Right to Left implication *)
    intros H.
    (* false = true is a contradiction *)
    discriminate H.
Qed.