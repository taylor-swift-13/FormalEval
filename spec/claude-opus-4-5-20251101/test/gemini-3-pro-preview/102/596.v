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

Example test_case : choose_num_spec 101 102 102.
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
           assert (k = 101 \/ k = 102) as Hk_cases by lia.
           destruct Hk_cases as [H101 | H102]; subst k.
           ++ vm_compute in Hk_even.
              discriminate.
           ++ lia.
    + intros Hnot_ex.
      exfalso.
      apply Hnot_ex.
      exists 102.
      split.
      * lia.
      * reflexivity.
Qed.