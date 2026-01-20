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

Example test_choose_num : choose_num_spec 17 21 20.
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
           assert (k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21) as Hcases by lia.
           destruct Hcases as [H17 | [H18 | [H19 | [H20 | H21]]]].
           --- subst k. compute in Heven. lia.
           --- lia.
           --- subst k. compute in Heven. lia.
           --- lia.
           --- subst k. compute in Heven. lia.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 18.
      split; [lia | reflexivity].
Qed.