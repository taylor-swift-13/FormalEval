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

Example test_digit_counts_125890 : even_odd_count_spec 125890 (3, 3).
Proof.
  unfold even_odd_count_spec.
  simpl.
  apply dc_step with (e:=2) (o:=3); [lia |].
  replace (Z.div 125890 10) with 12589%Z by reflexivity.
  apply dc_step with (e:=2) (o:=2); [lia |].
  replace (Z.div 12589 10) with 1258%Z by reflexivity.
  apply dc_step with (e:=1) (o:=2); [lia |].
  replace (Z.div 1258 10) with 125%Z by reflexivity.
  apply dc_step with (e:=1) (o:=1); [lia |].
  replace (Z.div 125 10) with 12%Z by reflexivity.
  apply dc_step with (e:=0) (o:=1); [lia |].
  replace (Z.div 12 10) with 1%Z by reflexivity.
  apply dc_base.
  lia.
Qed.