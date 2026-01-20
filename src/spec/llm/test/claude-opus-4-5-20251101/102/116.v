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

Example test_choose_num : choose_num_spec 1000 2000 2000.
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
           assert (k mod 2 = 0) as Hkeven by assumption.
           assert (2000 mod 2 = 0) as H2000even by reflexivity.
           destruct (Z.le_gt_cases k 2000) as [Hle2000 | Hgt2000].
           --- exact Hle2000.
           --- lia.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 2000.
      split; [lia | reflexivity].
Qed.