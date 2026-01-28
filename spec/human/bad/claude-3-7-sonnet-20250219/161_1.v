Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

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
  if is_lower_alpha a then my_uppercase a
  else if is_upper_alpha a then my_lowercase a
  else a.

Fixpoint contains_letter_dec (s : list ascii) : bool :=
  match s with
  | [] => false
  | h :: t => orb (is_letter_dec h) (contains_letter_dec t)
  end.

Definition solve_impl (s : string) : string :=
  let l := list_ascii_of_string s in
  if contains_letter_dec l
  then string_of_list_ascii (map change_case l)
  else string_of_list_ascii (rev l).

Example test_solve_AsDf :
  solve_impl "AsDf" = "aSdF".
Proof.
  unfold solve_impl.
  (* simplify list_ascii_of_string "AsDf" *)
  simpl.
  (* l = ["A"; "s"; "D"; "f"] *)
  set (l := ["A"; "s"; "D"; "f"]).
  (* compute contains_letter_dec l *)
  unfold contains_letter_dec.
  simpl.
  (* is_letter_dec "A" = true because 'A' is uppercase letter *)
  unfold is_letter_dec, is_lower_alpha, is_upper_alpha.
  simpl.
  (* "a" <=? "A" is false, so is_lower_alpha "A" = false *)
  (* "A" <=? "Z" is true, so is_upper_alpha "A" = true *)
  simpl.
  rewrite orb_true_l.
  simpl.

  (* contains_letter_dec l = true, so we do map change_case l *)
  unfold l; simpl.

  (* map change_case ["A"; "s"; "D"; "f"] *)

  (* change_case "A": is_upper_alpha true *)
  unfold change_case.
  unfold is_lower_alpha, is_upper_alpha.
  simpl.
  (* is_lower_alpha "A" = false *)
  (* is_upper_alpha "A" = true *)
  simpl.
  unfold my_lowercase.
  simpl.
  replace (nat_of_ascii "A" + 32) with 97 by reflexivity.
  simpl.
  (* change_case "A" = "a" *)

  (* change_case "s": is_lower_alpha true *)
  unfold change_case.
  unfold is_lower_alpha.
  simpl.
  (* "a" <=? "s" && "s" <=? "z" = true *)
  simpl.
  unfold my_uppercase.
  simpl.
  replace (nat_of_ascii "s" - 32) with 83 by reflexivity.
  simpl.
  (* change_case "s" = "S" *)

  (* change_case "D": is_upper_alpha true *)
  unfold change_case.
  unfold is_lower_alpha, is_upper_alpha.
  simpl.
  (* is_lower_alpha "D" = false *)
  (* is_upper_alpha "D" = true *)
  simpl.
  unfold my_lowercase.
  simpl.
  replace (nat_of_ascii "D" + 32) with 100 by reflexivity.
  simpl.
  (* change_case "D" = "d" *)

  (* change_case "f": is_lower_alpha true *)
  unfold change_case.
  unfold is_lower_alpha.
  simpl.
  unfold my_uppercase.
  simpl.
  replace (nat_of_ascii "f" - 32) with 70 by reflexivity.
  simpl.
  (* change_case "f" = "F" *)

  reflexivity.
Qed.