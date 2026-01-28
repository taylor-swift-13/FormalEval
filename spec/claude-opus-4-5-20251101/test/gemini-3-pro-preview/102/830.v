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

Example test_case : choose_num_spec 24 2003 2002.
Proof.
  unfold choose_num_spec.
  split.
  - intros H.
    lia.
  - intros Hle.
    split.
    + intros Hex.
      split.
      * reflexivity.
      * split.
        -- lia.
        -- intros k Hk_range Hk_even.
           assert (k < 2003 \/ k = 2003) by lia.
           destruct H as [Hlt | Heq].
           ++ lia.
           ++ subst k.
              vm_compute in Hk_even.
              discriminate.
    + intros Hnot_ex.
      exfalso.
      apply Hnot_ex.
      exists 24.
      split.
      * lia.
      * reflexivity.
Qed.