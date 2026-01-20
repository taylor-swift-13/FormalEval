Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition choose_num_spec (x y r : Z) : Prop :=
(x > y /\ r = -1) \/
(x <= y /\ (exists k : Z, r = 2 * k) /\ x <= r /\ r <= y /\
 (forall z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y -> z <= r)) \/
(x <= y /\ ~ (exists z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y) /\ r = -1).

Example test_choose_num : choose_num_spec 12 15 14.
Proof.
  unfold choose_num_spec.
  right. left.
  split.
  - lia.
  - split.
    + exists 7. reflexivity.
    + split.
      * lia.
      * split.
        -- lia.
        -- intros z [Heven [Hxz Hzy]].
           destruct Heven as [k Hk].
           (* z = 2*k, 12 <= z <= 15, so z in {12, 14} *)
           (* We need to show z <= 14 *)
           assert (12 <= 2*k <= 15) as Hbounds by lia.
           (* k must be 6 or 7, so z is 12 or 14 *)
           assert (k = 6 \/ k = 7) as Hk_cases by lia.
           destruct Hk_cases as [Hk6 | Hk7]; lia.
Qed.