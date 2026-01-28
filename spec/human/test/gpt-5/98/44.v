Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Open Scope string_scope.
Local Open Scope Z_scope.
Import ListNotations.

Definition is_uppercase_vowel_bool (c : ascii) : bool :=
  match c with
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition count_upper_impl (s : string) : nat :=
  length (filter (fun i : nat =>
    match String.get i s with
    | Some c => andb (Nat.even i) (is_uppercase_vowel_bool c)
    | None => false
    end) (seq 0 (String.length s))).

Definition problem_98_pre (s : string) : Prop := True.

Definition problem_98_spec (s : string) (output : nat) : Prop :=
  output = count_upper_impl s.

Example problem_98_test_spec :
  problem_98_spec "UUOIAEA" 4.
Proof.
  unfold problem_98_spec.
  vm_compute.
  reflexivity.
Qed.

Example problem_98_test_Z :
  Z.of_nat (count_upper_impl "UUOIAEA") = 4%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.