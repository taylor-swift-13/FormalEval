Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.
Require Import Coq.micromega.Lia.

Inductive digit_counts : Z -> nat -> nat -> Prop :=
| dc_base : forall n, (0 <= n < 10)%Z ->
    digit_counts n (if Z.even n then 1 else 0) (if Z.even n then 0 else 1)
| dc_step : forall n e o, (n >= 10)%Z ->
    digit_counts (Z.div n 10) e o ->
    digit_counts n (e + (if Z.even (Z.modulo n 10) then 1 else 0))
                   (o + (if Z.even (Z.modulo n 10) then 0 else 1)).

Definition even_odd_count_spec (num : Z) (res : nat * nat) : Prop :=
  let (even, odd) := res in
  digit_counts (Z.abs num) even odd.

Example test_digit_counts_2368 : even_odd_count_spec 2368 (3, 1).
Proof.
  unfold even_odd_count_spec.
  simpl.
  apply (dc_step 2368 2 1).
  - lia.
  - replace (Z.div 2368 10) with 236%Z by reflexivity.
    apply (dc_step 236 1 1).
    + lia.
    + replace (Z.div 236 10) with 23%Z by reflexivity.
      apply (dc_step 23 1 0).
      * lia.
      * replace (Z.div 23 10) with 2%Z by reflexivity.
        apply dc_base.
        lia.
Qed.