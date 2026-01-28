Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

Definition decode_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  let a := nat_of_ascii "a"%char in
  ascii_of_nat (a + (n - a + 21) mod 26).

Definition problem_50_pre (l' : string) : Prop := True.

Definition problem_50_spec (l' l : string) : Prop :=
  let list_l := list_ascii_of_string l in
  let list_l' := list_ascii_of_string l' in
  list_l = map decode_char list_l'.

Example problem_50_test_case :
  problem_50_pre (String "a"%char (String "b"%char (String "c"%char (String (ascii_of_nat 241) (String "w"%char (String "o"%char (String "r"%char (String "l"%char (String "d"%char (String (ascii_of_nat 241) (String "r"%char (String "l"%char (String "d"%char (String "y"%char (String "z"%char EmptyString))))))))))))))) ->
  problem_50_spec (String "a"%char (String "b"%char (String "c"%char (String (ascii_of_nat 241) (String "w"%char (String "o"%char (String "r"%char (String "l"%char (String "d"%char (String (ascii_of_nat 241) (String "r"%char (String "l"%char (String "d"%char (String "y"%char (String "z"%char EmptyString))))))))))))))) "vwxjrjmgyjmgytu".
Proof.
  intros _. unfold problem_50_spec.
  vm_compute.
  reflexivity.
Qed.