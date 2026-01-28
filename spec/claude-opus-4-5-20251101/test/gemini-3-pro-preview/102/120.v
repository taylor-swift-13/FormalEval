Require Import ZArith.
Require Import Psatz.
Open Scope Z_scope.

Definition choose_num_spec (x y result : Z) : Prop :=
  (x > y -> result = -1) /\
  (x <= y ->
    ((exists k, x <= k <= y /\ k mod 2 = 0) ->
      result mod 2 = 0 /\
      x <= result <= y /\
      (forall k, x <= k <= y -> k mod 2 = 0 -> k <= result)) /\
    ((~exists k, x <= k <= y /\ k mod 2 = 0) -> result = -1)).

Example test_case : choose_num_spec 18 31 30.
Proof.
  unfold choose_num_spec.
  split.
  - intros H. lia.
  - intros Hle.
    split.
    + intros Hex.
      split.
      * reflexivity.
      * split.
        -- lia.
        -- intros k Hk_range Hk_even.
           assert (k = 31 \/ k <= 30) by lia.
           destruct H as [H31 | H30].
           ++ subst k. vm_compute in Hk_even. discriminate.
           ++ lia.
    + intros Hnot_ex.
      exfalso.
      apply Hnot_ex.
      exists 18.
      split.
      * lia.
      * reflexivity.
Qed.