Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.

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

Example digitSum_uidRKhwDoJ_spec: digitSum_spec "uidRKhwDoJ" 299.
Proof.
  unfold digitSum_spec.
  compute.
  reflexivity.
Qed.

Example digitSum_uidRKhwDoJ_Z: Z.of_nat (digitSum_fun "uidRKhwDoJ") = 299%Z.
Proof.
  compute.
  reflexivity.
Qed.