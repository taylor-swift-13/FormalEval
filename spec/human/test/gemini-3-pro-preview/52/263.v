Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [8000001%Z; 1000%Z; 9999998%Z; 10000000%Z; 9000000%Z; 10%Z; 9999999%Z; 8000000%Z; 7000000%Z; 6000000%Z; 2000000%Z; 9999998%Z] 20%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    specialize (H 8000001%Z).
    assert (HIn : In 8000001%Z [8000001%Z; 1000%Z; 9999998%Z; 10000000%Z; 9000000%Z; 10%Z; 9999999%Z; 8000000%Z; 7000000%Z; 6000000%Z; 2000000%Z; 9999998%Z]).
    { simpl. left. reflexivity. }
    apply H in HIn.
    lia.
  - intros H.
    discriminate.
Qed.