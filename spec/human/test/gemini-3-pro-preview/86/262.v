Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Import ListNotations.
Open Scope string_scope.

(* Provided Definitions *)

Definition is_space_bool (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.eqb n 32) || (Nat.eqb n 9) || (Nat.eqb n 10) || (Nat.eqb n 11) || (Nat.eqb n 12) || (Nat.eqb n 13).

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

(* 
   Constructing the input string with explicit control characters:
   "passs " ++ Tab ++ Newline ++ FormFeed ++ " A B C..." 
*)
Definition test_input : string := 
  "passs " ++ String (ascii_of_nat 9) (String (ascii_of_nat 10) (String (ascii_of_nat 12) (" A B C   D E F     G H I      yintegramming"))).

Definition test_output : string := 
  "apsss " ++ String (ascii_of_nat 9) (String (ascii_of_nat 10) (String (ascii_of_nat 12) (" A B C   D E F     G H I      aeggiimmnnrty"))).

Example problem_86_test : problem_86_spec test_input test_output.
Proof.
  unfold problem_86_spec.
  unfold anti_shuffle_impl.
  vm_compute.
  reflexivity.
Qed.