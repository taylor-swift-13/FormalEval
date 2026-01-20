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
  - (* x > y -> result = -1 *)
    intro H. lia.
  - (* x <= y -> ... *)
    intro Hle.
    split.
    + (* exists even k -> result is max even in range *)
      intro Hexists.
      split.
      * (* 14 mod 2 = 0 *)
        reflexivity.
      * split.
        -- (* 12 <= 14 <= 15 *)
           lia.
        -- (* forall k in range, k even -> k <= 14 *)
           intros k Hrange Heven.
           destruct Hrange as [Hlo Hhi].
           (* k can be 12, 13, 14, or 15 *)
           (* even ones are 12 and 14 *)
           assert (k = 12 \/ k = 13 \/ k = 14 \/ k = 15) as Hcases by lia.
           destruct Hcases as [H12 | [H13 | [H14 | H15]]].
           --- lia.
           --- subst k. compute in Heven. lia.
           --- lia.
           --- subst k. compute in Heven. lia.
    + (* no even k -> result = -1 *)
      intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 14.
      split; [lia | reflexivity].
Qed.