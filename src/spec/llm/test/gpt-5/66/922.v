Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.

Local Open Scope string_scope.

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

Definition test_input : string :=
  "Th!s!s$0nly4t3switwhtabsBCDEFGHIJKLMNOPQRESTUVThis"
  ++ String (Ascii.ascii_of_nat 10) EmptyString
  ++ "is" ++ String (Ascii.ascii_of_nat 9) EmptyString ++ "a" ++ String (Ascii.ascii_of_nat 9) EmptyString
  ++ "tabstest" ++ String (Ascii.ascii_of_nat 9) EmptyString ++ "with"
  ++ String (Ascii.ascii_of_nat 10) EmptyString
  ++ "newlines" ++ String (Ascii.ascii_of_nat 9) EmptyString ++ "and" ++ String (Ascii.ascii_of_nat 9) EmptyString
  ++ "tabsWXYAThisZt!ng-f55S5t5b5t5m5t5nm5t4K5t5ms5t5m5t5nt5t5r5t1c&Def3@F5n".

Example digitSum_test_Z: Z.of_nat (digitSum_fun test_input) = 2632%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.