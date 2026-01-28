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

Example test_case : choose_num_spec 15 20 20.
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
           (* Since the range [15, 20] is small, we can enumerate cases for k *)
           assert (k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20) as Hk_cases by lia.
           destruct Hk_cases as [H15 | [H16 | [H17 | [H18 | [H19 | H20]]]]]; subst k.
           ++ (* k = 15 *)
              (* 15 is odd, contradicts Hk_even *)
              vm_compute in Hk_even.
              discriminate.
           ++ (* k = 16 *)
              lia.
           ++ (* k = 17 *)
              (* 17 is odd, contradicts Hk_even *)
              vm_compute in Hk_even.
              discriminate.
           ++ (* k = 18 *)
              lia.
           ++ (* k = 19 *)
              (* 19 is odd, contradicts Hk_even *)
              vm_compute in Hk_even.
              discriminate.
           ++ (* k = 20 *)
              lia.
    + (* Subcase: No even number exists in the range *)
      intros Hnot_ex.
      exfalso.
      apply Hnot_ex.
      exists 20.
      split.
      * lia.
      * reflexivity.
Qed.