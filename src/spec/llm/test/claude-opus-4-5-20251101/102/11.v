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

Example test_choose_num : choose_num_spec 50 60 60.
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
           assert (k mod 2 = 0 -> k <= 60) as Hgoal.
           {
             intro Hkeven.
             assert (k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 \/ k = 56 \/ k = 57 \/ k = 58 \/ k = 59 \/ k = 60) as Hcases by lia.
             destruct Hcases as [H50 | [H51 | [H52 | [H53 | [H54 | [H55 | [H56 | [H57 | [H58 | [H59 | H60]]]]]]]]]].
             --- lia.
             --- subst k. compute in Hkeven. lia.
             --- lia.
             --- subst k. compute in Hkeven. lia.
             --- lia.
             --- subst k. compute in Hkeven. lia.
             --- lia.
             --- subst k. compute in Hkeven. lia.
             --- lia.
             --- subst k. compute in Hkeven. lia.
             --- lia.
           }
           apply Hgoal. exact Heven.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 60.
      split; [lia | reflexivity].
Qed.