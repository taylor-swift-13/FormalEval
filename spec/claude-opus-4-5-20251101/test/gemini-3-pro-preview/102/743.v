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

Example test_case : choose_num_spec 100 102 102.
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
           (* Since the range [100, 102] is small, we can enumerate cases for k *)
           assert (k = 100 \/ k = 101 \/ k = 102) as Hk_cases by lia.
           destruct Hk_cases as [H100 | [H101 | H102]]; subst k.
           ++ (* k = 100 *)
              lia.
           ++ (* k = 101 *)
              (* 101 is odd, contradicts Hk_even *)
              vm_compute in Hk_even.
              discriminate.
           ++ (* k = 102 *)
              lia.
    + (* Subcase: No even number exists in the range *)
      intros Hnot_ex.
      exfalso.
      apply Hnot_ex.
      exists 100.
      split.
      * lia.
      * reflexivity.
Qed.