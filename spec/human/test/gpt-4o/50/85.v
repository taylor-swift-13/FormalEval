Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith. (* For nat arithmetic like mod *)
Import ListNotations.
Open Scope string_scope.

(* Helper function to convert a string to a list of ascii *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

(* Helper function to convert a list of ascii back to a string *)
Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (string_of_list_ascii l')
  end.

(* Decode a single character by shifting it 21 positions backwards *)
Definition decode_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  let a := nat_of_ascii "a"%char in
  ascii_of_nat (a + (n - a + 21) mod 26).

(* Precondition: no special constraints for `decode_shift` *)
Definition problem_50_pre (l' : string) : Prop := True.

(* Specification: decode a string encoded by shifting each character by 5 positions *)
Definition problem_50_spec (l' l : string) : Prop :=
  let list_l := list_ascii_of_string l in
  let list_l' := list_ascii_of_string l' in
  list_l = map decode_char list_l'.

(* Example proof for the test case *)
Example problem_50_test :
  problem_50_spec "cyhmtsgqyz" "xtchonbltu".
Proof.
  unfold problem_50_spec.
  simpl.
  reflexivity.
Qed.