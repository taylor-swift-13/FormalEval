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

Example test_choose_num : choose_num_spec 35 199 198.
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
           assert (Hk_bound: k <= 198 \/ k = 199) by lia.
           destruct Hk_bound as [Hle198 | Heq199].
           --- lia.
           --- subst k. 
               assert (199 mod 2 = 1) by reflexivity.
               lia.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 198.
      split; [lia | reflexivity].
Qed.