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

Example test_digit_counts_neg : even_odd_count_spec (-345821) (3, 3).
Proof.
  unfold even_odd_count_spec.
  simpl.
  apply dc_step with (e:=3) (o:=2); [lia |].
  replace (345821 / 10)%Z with 34582%Z by reflexivity.
  replace (345821 mod 10)%Z with 1%Z by reflexivity.
  simpl.
  apply dc_step with (e:=2) (o:=2); [lia |].
  replace (34582 / 10)%Z with 3458%Z by reflexivity.
  replace (34582 mod 10)%Z with 2%Z by reflexivity.
  simpl.
  apply dc_step with (e:=1) (o:=2); [lia |].
  replace (3458 / 10)%Z with 345%Z by reflexivity.
  replace (3458 mod 10)%Z with 8%Z by reflexivity.
  simpl.
  apply dc_step with (e:=1) (o:=1); [lia |].
  replace (345 / 10)%Z with 34%Z by reflexivity.
  replace (345 mod 10)%Z with 5%Z by reflexivity.
  simpl.
  apply dc_step with (e:=0) (o:=1); [lia |].
  replace (34 / 10)%Z with 3%Z by reflexivity.
  replace (34 mod 10)%Z with 4%Z by reflexivity.
  simpl.
  apply dc_base.
  lia.
Qed.