Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [1; 4; 7; 10] 6 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right: (forall x, In x [...] -> x < 6) -> false *)
    intros H.
    (* We find a counter-example in the list: 7 *)
    specialize (H 7).
    (* Prove 7 is in the list *)
    assert (In 7 [1; 4; 7; 10]) as HIn.
    { simpl. right. right. left. reflexivity. }
    apply H in HIn.
    lia.
  - (* Right to Left: false -> ... *)
    intros H.
    inversion H.
Qed.