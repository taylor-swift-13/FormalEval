Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [8000001; 9999998; 10000000; 9000000; 10; 9999999; 8000000; 7000000; 6000000; 2000000; 9999998] 20 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* We have (forall x, In x l -> x < 20). We need to prove False. *)
    (* We find a counterexample in the list, e.g., 8000001 *)
    specialize (H 8000001).
    (* Prove 8000001 is in the list *)
    assert (In 8000001 [8000001; 9999998; 10000000; 9000000; 10; 9999999; 8000000; 7000000; 6000000; 2000000; 9999998]) as HIn.
    { simpl. left. reflexivity. }
    apply H in HIn.
    (* Now we have 8000001 < 20, which is false *)
    lia.
  - (* Right to Left implication *)
    intros H.
    discriminate.
Qed.