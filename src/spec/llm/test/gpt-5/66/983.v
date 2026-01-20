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

Example digitSum_spec_case: digitSum_spec "HELLOthereWHATareYOUdoingTODAY?IHopeYOURdayISgoingWEL." 2186.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.

Example digitSum_Z_case: Z.of_nat (digitSum_fun "HELLOthereWHATareYOUdoingTODAY?IHopeYOURdayISgoingWEL.") = 2186%Z.
Proof.
  simpl.
  reflexivity.
Qed.