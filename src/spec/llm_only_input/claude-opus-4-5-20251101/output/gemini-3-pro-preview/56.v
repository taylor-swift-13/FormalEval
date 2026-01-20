Require Import List.
Require Import Bool.
Require Import Ascii.
Require Import String.
Import ListNotations.

(* Define a function to check if angle brackets are balanced *)
Fixpoint check_brackets (s : list ascii) (count : nat) : bool :=
  match s with
  | nil => Nat.eqb count 0
  | cons c rest =>
    if Ascii.eqb c "<"%char then
      check_brackets rest (S count)
    else if Ascii.eqb c ">"%char then
      match count with
      | O => false
      | S n => check_brackets rest n
      end
    else
      check_brackets rest count
  end.

(* Convert string to list of ascii *)
Definition string_to_list (s : string) : list ascii :=
  list_ascii_of_string s.

(* Main function to check if brackets in a string are balanced *)
Definition is_balanced (s : string) : bool :=
  check_brackets (string_to_list s) 0.

(* Function to check if all strings in a list have balanced brackets *)
Fixpoint all_balanced (l : list string) : bool :=
  match l with
  | nil => true
  | cons s rest => andb (is_balanced s) (all_balanced rest)
  end.

(* The test case: input = ["<>"], output = true *)
Example test_balanced : all_balanced ["<>"%string] = true.
Proof.
  unfold all_balanced.
  unfold is_balanced.
  unfold string_to_list.
  simpl.
  reflexivity.
Qed.