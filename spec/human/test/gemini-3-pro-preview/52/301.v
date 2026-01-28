Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [10000000; 9000000; 10000001; 10; 8000000; 6000000; 2000000; 10000001; 10000000] 10 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* We show a contradiction by finding an element >= 10 in the list *)
    assert (HIn : In 10000000 [10000000; 9000000; 10000001; 10; 8000000; 6000000; 2000000; 10000001; 10000000]).
    { simpl. left. reflexivity. }
    specialize (H 10000000 HIn).
    lia.
  - (* Right to Left implication *)
    intros H.
    discriminate.
Qed.