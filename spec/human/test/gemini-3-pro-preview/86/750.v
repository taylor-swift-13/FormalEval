Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

(* Provided Definitions *)

Definition is_space_bool (c : ascii) : bool :=
  if ascii_dec c " "%char then true else false.

Fixpoint insert_char (c : ascii) (s : string) : string :=
  match s with
  | EmptyString => String c EmptyString
  | String h t =>
      if Nat.leb (nat_of_ascii c) (nat_of_ascii h) then
        String c s
      else
        String h (insert_char c t)
  end.

Fixpoint sort_chars (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String h t => insert_char h (sort_chars t)
  end.

Fixpoint anti_shuffle_aux (s : string) (acc : string) : string :=
  match s with
  | EmptyString => sort_chars acc
  | String c rest =>
      if is_space_bool c then
        (sort_chars acc) ++ (String c EmptyString) ++ (anti_shuffle_aux rest EmptyString)
      else
        anti_shuffle_aux rest (String c acc)
  end.

Definition anti_shuffle_impl (s : string) : string :=
  anti_shuffle_aux s EmptyString.

Definition problem_86_pre (s : string) : Prop := True.

Definition problem_86_spec (s s_out : string) : Prop :=
  s_out = anti_shuffle_impl s.

(* Example Proof for Test Case *)

(* Helper definitions for non-printable characters to avoid unification errors *)
Definition tab := String (ascii_of_nat 9) EmptyString.
Definition nl := String (ascii_of_nat 10) EmptyString.
Definition vt := String (ascii_of_nat 11) EmptyString.
Definition ff := String (ascii_of_nat 12) EmptyString.

Definition s1 := "A B C   D E F     G H I      ".
Definition s2_in := "A B C   D EZYXWVUTSRQPONMLKJIHGFEDCBA F     G H I      Fk".
Definition s2_out := "A B C   D ABCDEEFGHIJKLMNOPQRSTUVWXYZ F     G H I      Fk".

(* Constructing input and output strings using helpers to ensure correct control character order *)
(* Input has ff (12) then vt (11) *)
Definition test_input := 
  "qui " ++ tab ++ nl ++ " " ++ tab ++ nl ++ ff ++ vt ++ s1 ++ ff ++ vt ++ s2_in.

(* Output has vt (11) then ff (12) because sort_chars sorts them ascending *)
Definition test_output := 
  "iqu " ++ tab ++ nl ++ " " ++ tab ++ nl ++ vt ++ ff ++ s1 ++ vt ++ ff ++ s2_out.

Example problem_86_test : problem_86_spec test_input test_output.
Proof.
  unfold problem_86_spec.
  unfold anti_shuffle_impl.
  vm_compute.
  reflexivity.
Qed.