Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Fixpoint Z_to_binary_aux (n : Z) (fuel : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
    if Z.eqb n 0 then ""
    else let bit := if Z.eqb (Z.modulo n 2) 0 then "0" else "1" in
         append (Z_to_binary_aux (Z.div n 2) fuel') bit
  end.

Definition Z_to_binary (n : Z) : string :=
  if Z.eqb n 0 then "0"
  else Z_to_binary_aux n (Z.to_nat n + 1).

Definition decimal_to_binary_spec (decimal : Z) (result : string) : Prop :=
  decimal >= 0 /\
  result = append "db" (append (Z_to_binary decimal) "db").

Lemma Z_to_binary_aux_succ : forall n f, 
  0 <= n -> 
  n < 2 ^ (Z.of_nat f) -> 
  Z_to_binary_aux n f = Z_to_binary_aux n (S f).
Proof.
  intros n f Hpos Hbound.
  revert n Hpos Hbound.
  induction f as [|f IH]; intros n Hpos Hbound.
  - simpl in Hbound. assert (n = 0) by lia. subst.
    simpl. reflexivity.
  - simpl. destruct (Z.eqb n 0) eqn:Heq.
    + reflexivity.
    + rewrite Znat.Nat2Z.inj_succ in Hbound.
      rewrite Z.pow_succ_r in Hbound by apply Nat2Z.is_nonneg.
      f_equal.
      apply IH.
      * apply Z.div_pos; lia.
      * apply Z.div_lt_upper_bound; try lia.
Qed.

Lemma Z_to_binary_aux_le : forall n f f', 
  0 <= n -> 
  n < 2 ^ (Z.of_nat f) -> 
  (f <= f')%nat -> 
  Z_to_binary_aux n f = Z_to_binary_aux n f'.
Proof.
  intros n f f' Hpos Hbound Hle.
  induction Hle.
  - reflexivity.
  - rewrite <- IHHle.
    apply Z_to_binary_aux_succ; try assumption.
    apply Z.lt_le_trans with (2 ^ Z.of_nat f).
    assumption.
    apply Z.pow_le_mono_r; try lia.
    apply Nat2Z.inj_le. assumption.
Qed.

Example test_case_1 : decimal_to_binary_spec 1000000000 "db111011100110101100101000000000db".
Proof.
  unfold decimal_to_binary_spec.
  split.
  - lia.
  - unfold Z_to_binary.
    replace (Z.eqb 1000000000 0) with false by reflexivity.
    match goal with
    | |- context [Z_to_binary_aux ?n ?fuel] =>
      replace (Z_to_binary_aux n fuel) with (Z_to_binary_aux n 60)
    end.
    + vm_compute. reflexivity.
    + apply Z_to_binary_aux_le.
      * lia.
      * vm_compute. reflexivity.
      * apply Nat2Z.inj_le. rewrite Nat2Z.inj_add. rewrite Z2Nat.id by lia. simpl. lia.
Qed.