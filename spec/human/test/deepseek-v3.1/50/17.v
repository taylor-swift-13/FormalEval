Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Import ListNotations.
Open Scope string_scope.

(* Convert string to list of ascii characters *)
Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list s'
  end.

(* Convert list of ascii characters back to string *)
Fixpoint list_to_string (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (list_to_string l')
  end.

(* Character decoding function *)
Definition decode_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  let a := nat_of_ascii "a"%char in
  ascii_of_nat (a + (n - a + 21) mod 26).

(* Specification *)
Definition problem_50_spec (input output : string) : Prop :=
  let input_list := string_to_list input in
  let output_list := string_to_list output in
  output_list = map decode_char input_list.

(* New test case proof *)
Example test_case_proof : problem_50_spec "zxlxfflljav" "usgsaaggevq".
Proof.
  unfold problem_50_spec.
  unfold string_to_list.
  compute.
  reflexivity.
Qed.