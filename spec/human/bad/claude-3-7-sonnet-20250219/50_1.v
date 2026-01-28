Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

(* Conversion between string and list ascii *)
Fixpoint list_ascii_of_string (s: string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (string_of_list_ascii l')
  end.

(* Lemmas relating the conversions *)
Lemma string_list_ascii_iso : forall s,
  string_of_list_ascii (list_ascii_of_string s) = s.
Proof.
  induction s; simpl; f_equal; assumption.
Qed.

Lemma list_ascii_string_iso : forall l,
  list_ascii_of_string (string_of_list_ascii l) = l.
Proof.
  induction l; simpl; f_equal; assumption.
Qed.

(* The decode_char function as specified *)
Definition decode_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  let a := nat_of_ascii "a"%char in
  ascii_of_nat (a + (n - a + 21) mod 26).

Definition problem_50_pre (l' : string) : Prop := True.

Definition problem_50_spec (l' l : string) : Prop :=
  let list_l := list_ascii_of_string l in
  let list_l' := list_ascii_of_string l' in
  list_l = map decode_char list_l'.

(* Test input and expected output *)
Definition input := "tantywccpjkimslotpzs".
Definition expected := "oviotrxxkefdhngjokun".

(* Auxiliary function to decode whole string *)
Fixpoint decode_string (s: string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (decode_char c) (decode_string s')
  end.

Example problem_50_test : problem_50_spec input expected.
Proof.
  unfold problem_50_spec.
  unfold input, expected.
  (* Simplify list conversion to lists *)
  remember (list_ascii_of_string expected) as l_expected.
  remember (list_ascii_of_string input) as l_input.

  (* The goal is l_expected = map decode_char l_input *)
  (* Equivalently, expected = decode_string input *)

  rewrite <- string_list_ascii_iso in Heql_expected.
  rewrite <- string_list_ascii_iso in Heql_input.

  subst l_expected l_input.

  (* So goal reduces to expected = decode_string input *)
  reflexivity.
Qed.