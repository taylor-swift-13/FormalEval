Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

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

Fixpoint string_of_nat_list (l : list nat) : string :=
  match l with
  | [] => EmptyString
  | x :: xs => String (Ascii.ascii_of_nat x) (string_of_nat_list xs)
  end.

Definition test_string : string :=
  string_of_nat_list
    [84; 104; 105; 115; 10; 105; 115; 9; 97; 9; 116; 101; 108; 115; 116; 9; 119; 105; 116; 104; 10; 110; 101; 119; 108; 105; 110; 101; 115; 9; 97; 110; 100; 9; 116; 97; 98; 115].

Example digitSum_spec_test: digitSum_spec test_string 84.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.

Example digitSum_test_Z: Z.of_nat (digitSum_fun test_string) = 84%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.