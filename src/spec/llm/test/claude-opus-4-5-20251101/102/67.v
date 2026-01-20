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

Example test_choose_num : choose_num_spec 15 29 28.
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
           assert (Hk: k mod 2 = 0) by assumption.
           assert (k <= 28 \/ k > 28) as Hcases by lia.
           destruct Hcases as [Hle28 | Hgt28].
           --- assumption.
           --- assert (k = 29) by lia.
               subst k. compute in Heven. lia.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 28.
      split; [lia | reflexivity].
Qed.