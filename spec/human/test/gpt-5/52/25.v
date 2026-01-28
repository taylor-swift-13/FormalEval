Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [-4%Z; -3%Z; -2%Z; 4%Z; -4%Z] (-1%Z) false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    exfalso.
    assert (Hin : In 4%Z [-4%Z; -3%Z; -2%Z; 4%Z; -4%Z]).
    { simpl. right. right. right. left. reflexivity. }
    specialize (H 4%Z Hin).
    lia.
  - intros Hfalse.
    exfalso.
    discriminate Hfalse.
Qed.