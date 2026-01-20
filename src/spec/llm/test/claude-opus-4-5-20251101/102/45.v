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

Example test_choose_num : choose_num_spec 11 14 14.
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
           assert (k = 11 \/ k = 12 \/ k = 13 \/ k = 14) as Hcases by lia.
           destruct Hcases as [H11 | [H12 | [H13 | H14]]].
           --- subst k. compute in Heven. lia.
           --- lia.
           --- subst k. compute in Heven. lia.
           --- lia.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 14.
      split; [lia | reflexivity].
Qed.