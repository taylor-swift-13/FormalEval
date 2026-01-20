Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.leb 65 n) && (Nat.leb n 90).

Fixpoint digitSum_calc (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' =>
      if is_upper c then (nat_of_ascii c) + (digitSum_calc s')
      else digitSum_calc s'
  end.

Definition digitSum_spec (s : string) (result : nat) : Prop :=
  result = digitSum_calc s.

Example digitSum_spec_empty_string_nat :
  digitSum_spec "" 0%nat.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.

Example digitSum_spec_empty_string_Z :
  Z.of_nat (digitSum_calc "") = 0%Z.
Proof.
  simpl.
  reflexivity.
Qed.