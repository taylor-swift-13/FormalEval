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

Example test_choose_num : choose_num_spec 1 6 6.
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
           assert (k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) as Hcases by lia.
           destruct Hcases as [H1 | [H2 | [H3 | [H4 | [H5 | H6]]]]].
           --- subst k. compute in Heven. lia.
           --- lia.
           --- subst k. compute in Heven. lia.
           --- lia.
           --- subst k. compute in Heven. lia.
           --- lia.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 6.
      split; [lia | reflexivity].
Qed.