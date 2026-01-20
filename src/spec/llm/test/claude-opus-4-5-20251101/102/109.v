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

Example test_choose_num : choose_num_spec 23 27 26.
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
           assert (k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) as Hcases by lia.
           destruct Hcases as [H23 | [H24 | [H25 | [H26 | H27]]]].
           --- subst k. compute in Heven. lia.
           --- lia.
           --- subst k. compute in Heven. lia.
           --- lia.
           --- subst k. compute in Heven. lia.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 26.
      split; [lia | reflexivity].
Qed.