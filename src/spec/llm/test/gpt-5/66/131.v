Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.

Fixpoint digitSum_fun (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String ch rest =>
      let code := nat_of_ascii ch in
      let is_upper := andb (Nat.leb 65 code) (Nat.leb code 90) in
      (if is_upper then code else 0) + digitSum_fun rest
  end.

Definition digitSum_spec (s : string) (sum : nat) : Prop :=
  sum = digitSum_fun s.

Example digitSum_uppercase_newlines_spec: digitSum_spec "ABCDEFGHIJKLMNOPQRSTUVWXYZnewlines"%string 2015.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.

Example digitSum_uppercase_newlines_Z: Z.of_nat (digitSum_fun "ABCDEFGHIJKLMNOPQRSTUVWXYZnewlines"%string) = 2015%Z.
Proof.
  simpl.
  reflexivity.
Qed.