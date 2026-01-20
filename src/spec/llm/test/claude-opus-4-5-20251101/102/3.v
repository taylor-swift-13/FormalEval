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

Example test_choose_num : choose_num_spec 33 12354 12354.
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
           assert (k mod 2 = 0) as Hkeven by assumption.
           assert (12354 mod 2 = 0) as H12354even by reflexivity.
           assert (k <= 12354 \/ k > 12354) as Hcases by lia.
           destruct Hcases as [Hle' | Hgt].
           --- exact Hle'.
           --- lia.
    + intro Hnoexists.
      exfalso.
      apply Hnoexists.
      exists 34.
      split; [lia | reflexivity].
Qed.