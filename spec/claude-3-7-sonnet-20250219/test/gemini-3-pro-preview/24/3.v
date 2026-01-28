Require Import ZArith.
Require Import Psatz.
Open Scope Z_scope.

Definition largest_divisor_spec (n d : Z) : Prop :=
  1 < n ->
  1 <= d < n /\
  n mod d = 0 /\
  (forall k, 1 < k < n -> n mod k = 0 -> k <= d).

Example test_case_10_5 : largest_divisor_spec 10 5.
Proof.
  unfold largest_divisor_spec.
  intros Hn.
  split.
  - lia.
  - split.
    + reflexivity.
    + intros k Hk_range Hk_mod.
      assert (k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9) as Hk_cases by lia.
      destruct Hk_cases as [? | [? | [? | [? | [? | [? | [? | ?]]]]]]]; subst k.
      * lia.
      * compute in Hk_mod. discriminate.
      * compute in Hk_mod. discriminate.
      * lia.
      * compute in Hk_mod. discriminate.
      * compute in Hk_mod. discriminate.
      * compute in Hk_mod. discriminate.
      * compute in Hk_mod. discriminate.
Qed.