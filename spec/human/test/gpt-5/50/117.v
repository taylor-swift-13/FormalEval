Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.
Open Scope Z_scope.

Definition decode_char (c : ascii) : ascii :=
  let n := Z.of_nat (nat_of_ascii c) in
  let a := Z.of_nat (nat_of_ascii "a"%char) in
  ascii_of_nat (Z.to_nat (a + Z.modulo (n - a + 21%Z) 26%Z)).

Definition problem_50_pre (l' : string) : Prop := True.

Definition problem_50_spec (l' l : string) : Prop :=
  let list_l := list_ascii_of_string l in
  let list_l' := list_ascii_of_string l' in
  list_l = map decode_char list_l'.

Example problem_50_test_case :
  problem_50_pre "worlencoded messagevtwxyz with shift" ->
  problem_50_spec "worlencoded messagevtwxyz with shift" "rjmgzixjyzyihznnvbzqorstuirdocincdao".
Proof.
  intros _. unfold problem_50_spec.
  vm_compute.
  reflexivity.
Qed.