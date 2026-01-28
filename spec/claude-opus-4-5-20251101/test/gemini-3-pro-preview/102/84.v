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

Example test_case : choose_num_spec 50 59 58.
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
           assert (k <= 58 \/ k = 59) as Hk_cases by lia.
           destruct Hk_cases as [Hle58 | Heq59].
           ++ (* k <= 58 *)
              exact Hle58.
           ++ (* k = 59 *)
              subst k.
              (* 59 is odd, contradicts Hk_even *)
              vm_compute in Hk_even.
              discriminate.
    + (* Subcase: No even number exists in the range *)
      intros Hnot_ex.
      exfalso.
      apply Hnot_ex.
      exists 50.
      split.
      * lia.
      * reflexivity.
Qed.