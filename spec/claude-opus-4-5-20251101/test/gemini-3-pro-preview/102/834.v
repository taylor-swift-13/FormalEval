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

Example test_case : choose_num_spec 22 27 26.
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
           (* Since the range [22, 27] is small, we can enumerate cases for k *)
           assert (k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) as Hk_cases by lia.
           destruct Hk_cases as [H22 | [H23 | [H24 | [H25 | [H26 | H27]]]]]; subst k.
           ++ (* k = 22 *)
              lia.
           ++ (* k = 23 *)
              (* 23 is odd, contradicts Hk_even *)
              vm_compute in Hk_even.
              discriminate.
           ++ (* k = 24 *)
              lia.
           ++ (* k = 25 *)
              (* 25 is odd, contradicts Hk_even *)
              vm_compute in Hk_even.
              discriminate.
           ++ (* k = 26 *)
              lia.
           ++ (* k = 27 *)
              (* 27 is odd, contradicts Hk_even *)
              vm_compute in Hk_even.
              discriminate.
    + (* Subcase: No even number exists in the range *)
      intros Hnot_ex.
      exfalso.
      apply Hnot_ex.
      exists 22.
      split.
      * lia.
      * reflexivity.
Qed.