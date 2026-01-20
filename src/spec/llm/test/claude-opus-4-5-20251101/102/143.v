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

Example test_choose_num : choose_num_spec 10 20 20.
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
           assert (k mod 2 = 0 -> k <= 20) as Hgoal.
           {
             intro Hev.
             assert (k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20) as Hcases by lia.
             destruct Hcases as [H10 | [H11 | [H12 | [H13 | [H14 | [H15 | [H16 | [H17 | [H18 | [H19 | H20]]]]]]]]]].
             --- lia.
             --- subst k. compute in Hev. lia.
             --- lia.
             --- subst k. compute in Hev. lia.
             --- lia.
             --- subst k. compute in Hev. lia.
             --- lia.
             --- subst k. compute in Hev. lia.
             --- lia.
             --- subst k. compute in Hev. lia.
             --- lia.
           }
           apply Hgoal. exact Heven.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 20.
      split; [lia | reflexivity].
Qed.