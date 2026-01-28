(* def solve(s):
"""You are given a string s.
if s[i] is a letter, reverse its case from lower to upper or vise versa,
otherwise keep it as it is.
If the string contains no letters, reverse the string.
The function should return the resulted string.
Examples
solve("1234") = "4321"
solve("ab") = "AB"
solve("#a@C") = "#A@c"
""" *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

Local Open Scope string_scope.

Definition is_lower_alpha (a : ascii) : bool :=
  (("a"%char <=? a)%char && (a <=? "z"%char)%char).

Definition is_upper_alpha (a : ascii) : bool :=
  (("A"%char <=? a)%char && (a <=? "Z"%char)%char).

Definition is_letter_dec (a : ascii) : bool :=
  is_lower_alpha a || is_upper_alpha a.

Definition my_uppercase (a : ascii) : ascii :=
  if is_lower_alpha a
  then ascii_of_nat (nat_of_ascii a - 32)
  else a.

Definition my_lowercase (a : ascii) : ascii :=
  if is_upper_alpha a
  then ascii_of_nat (nat_of_ascii a + 32)
  else a.

Definition change_case (a : ascii) : ascii :=
  if is_lower_alpha a then
    my_uppercase a
  else if is_upper_alpha a then
    my_lowercase a
  else
    a.

Fixpoint contains_letter_dec (s : list ascii) : bool :=
  match s with
  | [] => false
  | h :: t => is_letter_dec h || contains_letter_dec t
  end.

Definition solve_impl (s : string) : string :=
  let l := list_ascii_of_string s in
  if contains_letter_dec l
  then string_of_list_ascii (map change_case l)
  else string_of_list_ascii (rev l).

Definition problem_161_pre (s : string) : Prop := True.

Definition problem_161_spec (s s' : string) : Prop :=
  s' = solve_impl s.

(* Test case: input = ["tH1s Is A t3s AbttH1s Is A t3sT!GT!"], output = "Th1S iS a T3S aBTTh1S iS a T3St!gt!" *)
Example test_problem_161_tH1s_Is_A_t3s_AbttH1s_Is_A_t3sT_GT_ :
  problem_161_spec "tH1s Is A t3s AbttH1s Is A t3sT!GT!" "Th1S iS a T3S aBTTh1S iS a T3St!gt!".
Proof.
  unfold problem_161_spec.
  vm_compute.
  reflexivity.
Qed.