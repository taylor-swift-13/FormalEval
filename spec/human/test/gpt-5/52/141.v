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
  problem_52_spec [2000000%Z; 10000000%Z; 9000000%Z; 10%Z; 200%Z; 7000000%Z; 6000000%Z; 2000000%Z] 10000000%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    exfalso.
    assert (Hlt : 10000000%Z < 10000000%Z).
    { apply H. simpl. right. left. reflexivity. }
    lia.
  - intros Hfalse. intros x HIn.
    exfalso. discriminate Hfalse.
Qed.