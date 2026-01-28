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
  problem_52_spec [-3%Z; -2%Z; 4%Z; 4%Z; -2%Z] 0%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros Hall. exfalso.
    assert (HIn : In 4%Z [-3%Z; -2%Z; 4%Z; 4%Z; -2%Z]).
    { simpl. right. right. left. reflexivity. }
    pose proof (Hall 4%Z HIn) as Hlt.
    assert (0 <= 4)%Z by lia.
    lia.
  - intros H.
    intros x HIn.
    exfalso. discriminate H.
Qed.