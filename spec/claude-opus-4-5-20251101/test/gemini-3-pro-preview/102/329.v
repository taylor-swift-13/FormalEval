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

Example test_case : choose_num_spec 1 99 98.
Proof.
  unfold choose_num_spec.
  split.
  - (* Case x > y *)
    intros H.
    lia.
  - (* Case x <= y *)
    intros Hle.
    split.
    + (* Subcase: An even number exists in the range *)
      intros Hex.
      split.
      * (* Prove result mod 2 = 0 *)
        reflexivity.
      * split.
        -- (* Prove x <= result <= y *)
           lia.
        -- (* Prove result is the maximum even number in range *)
           intros k Hk_range Hk_even.
           (* We need to show k <= 98. Since k <= 99, we check if k = 99 *)
           destruct (Z.eq_dec k 99) as [Heq | Hneq].
           ++ (* k = 99 *)
              subst k.
              (* 99 is odd, contradicts Hk_even *)
              vm_compute in Hk_even.
              discriminate.
           ++ (* k <> 99 implies k <= 98 *)
              lia.
    + (* Subcase: No even number exists in the range *)
      intros Hnot_ex.
      exfalso.
      apply Hnot_ex.
      exists 98.
      split.
      * lia.
      * reflexivity.
Qed.