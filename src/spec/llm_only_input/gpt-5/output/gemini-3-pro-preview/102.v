Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition choose_num_spec (x y result : Z) : Prop :=
  (result = -1 <-> (forall n : Z, x <= n <= y -> Z.Odd n)) /\
  (result <> -1 -> 
     Z.Even result /\ 
     x <= result <= y /\ 
     (forall n : Z, x <= n <= y -> Z.Even n -> n <= result)).

Example choose_num_spec_test_1215_14 : choose_num_spec 12%Z 15%Z 14%Z.
Proof.
  unfold choose_num_spec.
  split.
  - split.
    + intros H.
      exfalso.
      lia.
    + intros H.
      exfalso.
      specialize (H 12%Z).
      assert (12%Z <= 12%Z <= 15%Z) as Hrange by lia.
      specialize (H Hrange).
      destruct H as [k Hk].
      lia.
  - intros Hne.
    split.
    + exists 7%Z.
      lia.
    + split.
      * lia.
      * intros n Hrange Heven.
        destruct Heven as [k Hk].
        subst n.
        assert (k <= 7)%Z by lia.
        lia.
Qed.