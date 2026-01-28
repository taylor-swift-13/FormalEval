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

Definition eqb_ascii (x y : ascii) : bool :=
  if ascii_dec x y then true else false.

Fixpoint group_utf8 (l : list ascii) : list (list ascii) :=
  match l with
  | [] => []
  | a :: b :: c :: d :: t =>
      if eqb_ascii a (ascii_of_nat 240)
      then (a :: b :: c :: d :: []) :: group_utf8 t
      else (a :: []) :: group_utf8 (b :: c :: d :: t)
  | a :: t => (a :: []) :: group_utf8 t
  end.

Fixpoint concat_ascii (ll : list (list ascii)) : list ascii :=
  match ll with
  | [] => []
  | h :: t => h ++ concat_ascii t
  end.

Definition reverse_by_utf8 (l : list ascii) : list ascii :=
  concat_ascii (rev (group_utf8 l)).

Definition solve_impl (s : string) : string :=
  let l := list_ascii_of_string s in
  if contains_letter_dec l
  then string_of_list_ascii (map change_case l)
  else string_of_list_ascii (reverse_by_utf8 l).

Definition problem_161_pre (s : string) : Prop := True.

Definition problem_161_spec (s s' : string) : Prop :=
  s' = solve_impl s.

Example test_problem_161_emoji :
  problem_161_spec
    (string_of_list_ascii
       [ascii_of_nat 240; ascii_of_nat 159; ascii_of_nat 152; ascii_of_nat 130;
        ascii_of_nat 240; ascii_of_nat 159; ascii_of_nat 152; ascii_of_nat 142;
        ascii_of_nat 240; ascii_of_nat 159; ascii_of_nat 152; ascii_of_nat 128;
        ascii_of_nat 240; ascii_of_nat 159; ascii_of_nat 152; ascii_of_nat 130;
        ascii_of_nat 240; ascii_of_nat 159; ascii_of_nat 152; ascii_of_nat 142])
    (string_of_list_ascii
       [ascii_of_nat 240; ascii_of_nat 159; ascii_of_nat 152; ascii_of_nat 142;
        ascii_of_nat 240; ascii_of_nat 159; ascii_of_nat 152; ascii_of_nat 130;
        ascii_of_nat 240; ascii_of_nat 159; ascii_of_nat 152; ascii_of_nat 128;
        ascii_of_nat 240; ascii_of_nat 159; ascii_of_nat 152; ascii_of_nat 142;
        ascii_of_nat 240; ascii_of_nat 159; ascii_of_nat 152; ascii_of_nat 130]).
Proof.
  unfold problem_161_spec.
  vm_compute.
  reflexivity.
Qed.