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

Example test_choose_num : choose_num_spec 1 15 14.
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
           assert (Hk: k mod 2 = 0 -> k <= 14 \/ k > 14) by lia.
           destruct (Z.le_gt_cases k 14) as [Hle14 | Hgt14].
           --- exact Hle14.
           --- assert (k = 15) by lia.
               subst k. compute in Heven. lia.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 14.
      split; [lia | reflexivity].
Qed.