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

Example test_choose_num : choose_num_spec 100 200 200.
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
           assert (Hk_even: k mod 2 = 0) by assumption.
           assert (200 mod 2 = 0) by reflexivity.
           destruct (Z.eq_dec (k mod 2) 0) as [Hmod | Hmod].
           --- lia.
           --- contradiction.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 200.
      split; [lia | reflexivity].
Qed.