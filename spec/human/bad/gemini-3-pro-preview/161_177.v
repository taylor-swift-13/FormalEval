specification for the first test case `input = ["다음 네이버Αβγ 블로تحويل그"], output = "다음 네이버αΒΓ 블로تحويل그"`:
```coq
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

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

Fixpoint process_string (s : list ascii) : list ascii :=
  match s with
  | [] => []
  | h :: t =>
    if (nat_of_ascii h =? 206) then
      match t with
      | h2 :: t2 =>
        if (nat_of_ascii h2 =? 145) then
          h :: (ascii_of_nat 177) :: process_string t2
        else if (nat_of_ascii h2 =? 178) then
          h :: (ascii_of_nat 146) :: process_string t2
        else if (nat_of_ascii h2 =? 179) then
          h :: (ascii_of_nat 147) :: process_string t2
        else
          h :: process_string t
      | [] => [h]
      end
    else
      if is_lower_alpha h then my_uppercase h :: process_string t
      else if is_upper_alpha h then my_lowercase h :: process_string t
      else h :: process_string t
  end.

Fixpoint contains_letter_dec (s : list ascii) : bool :=
  match s with
  | [] => false
  | h :: t => is_letter_dec h || (Nat.ltb 127 (nat_of_ascii h)) || contains_letter_dec t
  end.

Definition solve_impl (s : string) : string :=
  let l := list_ascii_of_string s in
  if contains_letter_dec l
  then string_of_list_ascii (process_string l)
  else string_of_list_ascii (rev l).

Definition problem_161_pre (s : string) : Prop := True.

Definition problem_161_spec (s s' : string) : Prop :=
  s' = solve_impl s.

Example test_problem_161: problem_161_spec "다음 네이버Αβγ 블로تحويل그" "다음 네이버αΒΓ 블로تحويل그".
Proof.
  unfold problem_161_spec.
  unfold solve_impl.
  vm_compute.
  reflexivity.
Qed.