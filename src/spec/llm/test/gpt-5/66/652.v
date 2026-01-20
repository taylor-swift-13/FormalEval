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

Definition input_string :=
  "witwhtabsBCDEFGHIJKLMNOPQRSTUVThis"
  ++ String (ascii_of_nat 10) EmptyString
  ++ "is"
  ++ String (ascii_of_nat 9) EmptyString
  ++ "a"
  ++ String (ascii_of_nat 9) EmptyString
  ++ "test"
  ++ String (ascii_of_nat 9) EmptyString
  ++ "with"
  ++ String (ascii_of_nat 10) EmptyString
  ++ "newlines"
  ++ String (ascii_of_nat 9) EmptyString
  ++ "and"
  ++ String (ascii_of_nat 9) EmptyString
  ++ "tabsWXYAThisZ".

Example digitSum_input_spec: digitSum_spec input_string 2183.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.

Example digitSum_input_Z: Z.of_nat (digitSum_fun input_string) = 2183%Z.
Proof.
  simpl.
  reflexivity.
Qed.