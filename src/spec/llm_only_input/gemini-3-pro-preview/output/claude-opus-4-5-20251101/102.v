Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition choose_num_spec (x y result : Z) : Prop :=
  (x > y -> result = -1) /\
  (x <= y ->
    ((exists k, x <= k <= y /\ k mod 2 = 0) ->
      result mod 2 = 0 /\
      x <= result <= y /\
      (forall k, x <= k <= y -> k mod 2 = 0 -> k <= result)) /\
    ((~exists k, x <= k <= y /\ k mod 2 = 0) -> result = -1)).

Example test_choose_num : choose_num_spec 12 15 14.
Proof.
  unfold choose_num_spec.
  split.
  - (* Case: x > y implies result = -1 *)
    intros Hgt.
    (* 12 > 15 is false, so the implication holds trivially *)
    lia.
  - (* Case: x <= y *)
    intros Hle.
    split.
    + (* Subcase: An even number exists in range *)
      intros Hex.
      split.
      * (* Prove result is even: 14 mod 2 = 0 *)
        reflexivity.
      * split.
        -- (* Prove result is in range: 12 <= 14 <= 15 *)
           lia.
        -- (* Prove result is the largest even number *)
           intros k Hk_range Hk_even.
           (* Since the range is small, we can check each integer in [12, 15] *)
           assert (k = 12 \/ k = 13 \/ k = 14 \/ k = 15) as Hk_cases by lia.
           destruct Hk_cases as [H12 | [H13 | [H14 | H15]]]; subst k.
           ++ (* k = 12 *)
              lia.
           ++ (* k = 13 *)
              (* 13 is odd, so Hk_even (13 mod 2 = 0) is false *)
              assert (Hodd: 13 mod 2 = 1) by reflexivity.
              rewrite Hodd in Hk_even.
              discriminate.
           ++ (* k = 14 *)
              lia.
           ++ (* k = 15 *)
              (* 15 is odd, so Hk_even (15 mod 2 = 0) is false *)
              assert (Hodd: 15 mod 2 = 1) by reflexivity.
              rewrite Hodd in Hk_even.
              discriminate.
    + (* Subcase: No even number exists in range *)
      intros Hnot_ex.
      (* This premise is false because 12 is even and in range *)
      exfalso.
      apply Hnot_ex.
      exists 12.
      split.
      * lia.
      * reflexivity.
Qed.