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

Example test_choose_num : choose_num_spec 31 99 98.
Proof.
  unfold choose_num_spec.
  split.
  - intro H. lia.
  - intro Hle.
    split.
    + intro Hexists.
      split.
      * reflexivity.
      * split.
        -- lia.
        -- intros k Hrange Heven.
           destruct Hrange as [Hlo Hhi].
           assert (k mod 2 = 0 -> k <= 98 \/ k > 98) as Hdec by lia.
           destruct (Z.le_gt_cases k 98) as [Hle98 | Hgt98].
           --- exact Hle98.
           --- assert (k >= 99) by lia.
              assert (k = 99) by lia.
              subst k.
              compute in Heven.
              lia.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 98.
      split; [lia | reflexivity].
Qed.