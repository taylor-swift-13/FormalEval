Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

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
  "This" ++ String (ascii_of_nat 10) (
  "is" ++ String (ascii_of_nat 9) (
  "a" ++ String (ascii_of_nat 9) (
  "test" ++ String (ascii_of_nat 9) (
  "with" ++ String (ascii_of_nat 10) (
  "ntestestabsWXThiAThiswlines" ++ String (ascii_of_nat 9) (
  "and" ++ String (ascii_of_nat 9) 
  "tabsWDXYZtabs")))))).

Example test_digitSum_complex: digitSum_spec test_input 914.
Proof.
  unfold digitSum_spec, test_input.
  vm_compute.
  reflexivity.
Qed.