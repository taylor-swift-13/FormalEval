Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

Definition ascii_code (c : ascii) : nat := nat_of_ascii c.

Definition is_upper (c : ascii) : bool :=
  let n := ascii_code c in andb (Nat.leb 65 n) (Nat.leb n 90).

Definition is_lower (c : ascii) : bool :=
  let n := ascii_code c in andb (Nat.leb 97 n) (Nat.leb n 122).

Definition is_alpha (c : ascii) : bool := orb (is_upper c) (is_lower c).

Definition swapcase_char (c : ascii) : ascii :=
  let n := ascii_code c in
  if is_lower c then ascii_of_nat (n - 32)
  else if is_upper c then ascii_of_nat (n + 32)
  else c.

Fixpoint string_map (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (string_map f s')
  end.

Fixpoint has_letter (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c s' => orb (is_alpha c) (has_letter s')
  end.

Fixpoint string_rev_aux (s acc : string) : string :=
  match s with
  | EmptyString => acc
  | String c s' => string_rev_aux s' (String c acc)
  end.

Definition string_rev (s : string) : string := string_rev_aux s EmptyString.

Fixpoint swapcase_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
    let n := ascii_code c in
    if andb (Nat.leb 206 n) (Nat.leb n 206) (* lead byte for Greek letters in UTF-8 *)
    then
      match s' with
      | EmptyString => String c EmptyString
      | String d s'' =>
        let nd := ascii_code d in
        if andb (Nat.leb 145 nd) (Nat.leb nd 169) (* Greek uppercase second byte range *)
        then String c (String (ascii_of_nat (nd + 32)) (swapcase_string s''))
        else if andb (Nat.leb 177 nd) (Nat.leb nd 201) (* Greek lowercase second byte range *)
        then String c (String (ascii_of_nat (nd - 32)) (swapcase_string s''))
        else String c (String d (swapcase_string s''))
      end
    else
      if andb (Nat.leb 97 n) (Nat.leb n 122)
      then String (ascii_of_nat (n - 32)) (swapcase_string s')
      else if andb (Nat.leb 65 n) (Nat.leb n 90)
      then String (ascii_of_nat (n + 32)) (swapcase_string s')
      else String c (swapcase_string s')
  end.

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter s
  then r = swapcase_string s
  else r = string_rev s.

Example solve_spec_multilang :
  solve_spec ("الअअমুকΑβγুabcdefলমlxYMHvkfUু"%string)
             ("الअअমুকαΒΓুABCDEFলমLXymhVKFuু"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.