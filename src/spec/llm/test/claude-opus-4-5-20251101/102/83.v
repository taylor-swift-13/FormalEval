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

Example test_choose_num : choose_num_spec 6 15 14.
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
           assert (k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15) as Hcases by lia.
           destruct Hcases as [H6 | [H7 | [H8 | [H9 | [H10 | [H11 | [H12 | [H13 | [H14 | H15]]]]]]]]].
           --- lia.
           --- subst k. compute in Heven. lia.
           --- lia.
           --- subst k. compute in Heven. lia.
           --- lia.
           --- subst k. compute in Heven. lia.
           --- lia.
           --- subst k. compute in Heven. lia.
           --- lia.
           --- subst k. compute in Heven. lia.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 14.
      split; [lia | reflexivity].
Qed.