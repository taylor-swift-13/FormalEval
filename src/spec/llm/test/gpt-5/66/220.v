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

Definition nl := String (Ascii.ascii_of_nat 10) EmptyString.
Definition tab := String (Ascii.ascii_of_nat 9) EmptyString.

Definition test_str :=
  "isThis" ++ nl ++ "is" ++ tab ++ "a" ++ tab ++ "test" ++ tab ++ "with" ++ nl ++ "newlines" ++ tab ++ "and" ++ tab ++ "tabs".

Example digitSum_new_spec: digitSum_spec test_str 84.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.

Example digitSum_new_Z: Z.of_nat (digitSum_fun test_str) = 84%Z.
Proof.
  simpl.
  reflexivity.
Qed.