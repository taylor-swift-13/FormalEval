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
  problem_52_spec [2%Z; 4%Z; 6%Z; 8%Z] 7%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros HAll.
    exfalso.
    assert (Hlt : 8 < 7).
    { apply HAll.
      simpl. right. right. right. left. reflexivity. }
    lia.
  - intros Hout.
    intros x HIn.
    exfalso.
    discriminate Hout.
Qed.