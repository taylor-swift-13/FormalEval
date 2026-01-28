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

Definition is_cyr_upper_pair (a b : ascii) : bool :=
  let na := nat_of_ascii a in
  let nb := nat_of_ascii b in
  (Nat.eqb na 208 && Nat.leb 144 nb && Nat.leb nb 175) ||
  (Nat.eqb na 208 && Nat.eqb nb 129).

Definition is_cyr_lower_pair (a b : ascii) : bool :=
  let na := nat_of_ascii a in
  let nb := nat_of_ascii b in
  (Nat.eqb na 208 && Nat.leb 176 nb && Nat.leb nb 191) ||
  (Nat.eqb na 209 && Nat.leb 128 nb && Nat.leb nb 143) ||
  (Nat.eqb na 209 && Nat.eqb nb 145).

Definition cyr_upper_to_lower (a b : ascii) : list ascii :=
  let na := nat_of_ascii a in
  let nb := nat_of_ascii b in
  if (Nat.eqb na 208) && (Nat.leb 144 nb && Nat.leb nb 159) then
    [ascii_of_nat 208; ascii_of_nat (nb + 32)]
  else if (Nat.eqb na 208) && (Nat.leb 160 nb && Nat.leb nb 175) then
    [ascii_of_nat 209; ascii_of_nat (nb - 32)]
  else if (Nat.eqb na 208) && (Nat.eqb nb 129) then
    [ascii_of_nat 209; ascii_of_nat 145]
  else [a; b].

Definition cyr_lower_to_upper (a b : ascii) : list ascii :=
  let na := nat_of_ascii a in
  let nb := nat_of_ascii b in
  if (Nat.eqb na 208) && (Nat.leb 176 nb && Nat.leb nb 191) then
    [ascii_of_nat 208; ascii_of_nat (nb - 32)]
  else if (Nat.eqb na 209) && (Nat.leb 128 nb && Nat.leb nb 143) then
    [ascii_of_nat 208; ascii_of_nat (nb + 32)]
  else if (Nat.eqb na 209) && (Nat.eqb nb 145) then
    [ascii_of_nat 208; ascii_of_nat 129]
  else [a; b].

Fixpoint map_change_case_utf8 (s : list ascii) : list ascii :=
  match s with
  | [] => []
  | a :: t =>
      if is_lower_alpha a then my_uppercase a :: map_change_case_utf8 t
      else if is_upper_alpha a then my_lowercase a :: map_change_case_utf8 t
      else match t with
           | b :: t2 =>
               if is_cyr_upper_pair a b then
                 cyr_upper_to_lower a b ++ map_change_case_utf8 t2
               else if is_cyr_lower_pair a b then
                 cyr_lower_to_upper a b ++ map_change_case_utf8 t2
               else a :: map_change_case_utf8 t
           | [] => [a]
           end
  end.

Fixpoint contains_letter_utf8 (s : list ascii) : bool :=
  match s with
  | [] => false
  | a :: t =>
      is_letter_dec a ||
      match t with
      | b :: t2 =>
          is_cyr_upper_pair a b || is_cyr_lower_pair a b || contains_letter_utf8 t
      | [] => contains_letter_utf8 t
      end
  end.

Definition solve_impl (s : string) : string :=
  let l := list_ascii_of_string s in
  if contains_letter_utf8 l
  then string_of_list_ascii (map_change_case_utf8 l)
  else string_of_list_ascii (rev l).

Definition problem_161_pre (s : string) : Prop := True.

Definition problem_161_spec (s s' : string) : Prop :=
  s' = solve_impl s.

Example test_problem_161_cyr :
  problem_161_spec "Это тестовая строка" "эТО ТЕСТОВАЯ СТРОКА".
Proof.
  unfold problem_161_spec.
  vm_compute.
  reflexivity.
Qed.