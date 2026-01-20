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

Definition test_string : string :=
  "tabsBCDEFGHIJKLMNOPQRSTUVThis"%string
  ++ String (ascii_of_nat 10) EmptyString
  ++ "is"%string
  ++ String (ascii_of_nat 9) EmptyString
  ++ "a"%string
  ++ String (ascii_of_nat 9) EmptyString
  ++ "test"%string
  ++ String (ascii_of_nat 9) EmptyString
  ++ "tabsWDXYZ"%string.

Example digitSum_tabs_spec: digitSum_spec test_string 2102.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.

Example digitSum_tabs_Z: Z.of_nat (digitSum_fun test_string) = 2102%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.