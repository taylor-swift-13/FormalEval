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

Example test_choose_num : choose_num_spec 35 101 100.
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
           assert (k mod 2 = 0 -> k <= 100 \/ k > 100) as Hdec by lia.
           destruct (Z.le_gt_cases k 100) as [Hle' | Hgt].
           --- exact Hle'.
           --- assert (k >= 101) by lia.
              assert (k = 101) by lia.
              subst k.
              compute in Heven.
              lia.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 100.
      split; [lia | reflexivity].
Qed.