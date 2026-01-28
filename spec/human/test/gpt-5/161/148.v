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

Definition toggle_greek_pair (b1 b2 : nat) : option (nat * nat) :=
  if Nat.eqb b1 206 then
    if (Nat.eqb b2 145) || (Nat.eqb b2 146) || (Nat.eqb b2 147)
    then Some (206, b2 + 32)
    else if (Nat.eqb b2 177) || (Nat.eqb b2 178) || (Nat.eqb b2 179)
    then Some (206, b2 - 32)
    else None
  else None.

Definition toggle_utf8_pair (a1 a2 : ascii) : option (ascii * ascii) :=
  let b1 := nat_of_ascii a1 in
  let b2 := nat_of_ascii a2 in
  match toggle_greek_pair b1 b2 with
  | Some (x1, x2) => Some (ascii_of_nat x1, ascii_of_nat x2)
  | None => None
  end.

Fixpoint contains_letter_dec (s : list ascii) : bool :=
  match s with
  | [] => false
  | h :: t =>
      if is_letter_dec h then true
      else match t with
           | h2 :: t' =>
               let b1 := nat_of_ascii h in
               let b2 := nat_of_ascii h2 in
               match toggle_greek_pair b1 b2 with
               | Some _ => true
               | None => contains_letter_dec t
               end
           | [] => false
           end
  end.

Fixpoint process_bytes (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | h :: t =>
      if is_lower_alpha h then my_uppercase h :: process_bytes t
      else if is_upper_alpha h then my_lowercase h :: process_bytes t
      else match t with
           | h2 :: t' =>
               match toggle_utf8_pair h h2 with
               | Some (x1, x2) => x1 :: x2 :: process_bytes t'
               | None => h :: process_bytes t
               end
           | [] => [h]
           end
  end.

Definition solve_impl (s : string) : string :=
  let l := list_ascii_of_string s in
  if contains_letter_dec l
  then string_of_list_ascii (process_bytes l)
  else string_of_list_ascii (rev l).

Definition problem_161_pre (s : string) : Prop := True.

Definition problem_161_spec (s s' : string) : Prop :=
  s' = solve_impl s.

Example test_problem_161_case :
  problem_161_spec "الحالअअমুকΑβγুলমুমলাত" "الحالअअমুকαΒΓুলমুমলাত".
Proof.
  unfold problem_161_spec.
  vm_compute.
  reflexivity.
Qed.