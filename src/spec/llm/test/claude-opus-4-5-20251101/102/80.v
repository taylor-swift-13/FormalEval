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

Example test_choose_num : choose_num_spec 30 50 50.
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
           assert (Hk_mod: k mod 2 = 0) by assumption.
           assert (50 mod 2 = 0) as H50even by reflexivity.
           destruct (Z.eq_dec (k mod 2) 0) as [Hkeven | Hkodd].
           --- assert (k <= 50 \/ k > 50) as Hcmp by lia.
               destruct Hcmp as [Hle50 | Hgt50].
               ---- lia.
               ---- lia.
           --- lia.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 50.
      split; [lia | reflexivity].
Qed.