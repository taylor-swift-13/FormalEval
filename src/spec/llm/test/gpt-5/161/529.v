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

Fixpoint swapcase_utf8 (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c1 s' =>
      let n1 := ascii_code c1 in
      if is_lower c1 then String (ascii_of_nat (n1 - 32)) (swapcase_utf8 s')
      else if is_upper c1 then String (ascii_of_nat (n1 + 32)) (swapcase_utf8 s')
      else if Nat.eqb n1 206 (* 0xCE: Greek *) then
        match s' with
        | String c2 s'' =>
            let n2 := ascii_code c2 in
            if andb (Nat.leb 145 n2) (Nat.leb n2 169) (* Α..Ω subset *)
            then String c1 (String (ascii_of_nat (n2 + 32)) (swapcase_utf8 s''))
            else if andb (Nat.leb 177 n2) (Nat.leb n2 191) (* α.. range within CE *)
            then String c1 (String (ascii_of_nat (n2 - 32)) (swapcase_utf8 s''))
            else String c1 (swapcase_utf8 s')
        | _ => String c1 (swapcase_utf8 s')
        end
      else if Nat.eqb n1 208 (* 0xD0: Cyrillic lead *) then
        match s' with
        | String c2 s'' =>
            let n2 := ascii_code c2 in
            if andb (Nat.leb 144 n2) (Nat.leb n2 159) (* А..П *)
            then String c1 (String (ascii_of_nat (n2 + 32)) (swapcase_utf8 s''))
            else if andb (Nat.leb 160 n2) (Nat.leb n2 175) (* Р..Я *)
            then String (ascii_of_nat 209) (String (ascii_of_nat (n2 - 32)) (swapcase_utf8 s''))
            else if andb (Nat.leb 176 n2) (Nat.leb n2 191) (* а..п *)
            then String c1 (String (ascii_of_nat (n2 - 32)) (swapcase_utf8 s''))
            else String c1 (swapcase_utf8 s')
        | _ => String c1 (swapcase_utf8 s')
        end
      else if Nat.eqb n1 209 (* 0xD1: Cyrillic lead for lower half *) then
        match s' with
        | String c2 s'' =>
            let n2 := ascii_code c2 in
            if andb (Nat.leb 128 n2) (Nat.leb n2 143) (* р..я *)
            then String (ascii_of_nat 208) (String (ascii_of_nat (n2 + 32)) (swapcase_utf8 s''))
            else String c1 (swapcase_utf8 s')
        | _ => String c1 (swapcase_utf8 s')
        end
      else String c1 (swapcase_utf8 s')
  end.

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter s
  then r = swapcase_utf8 s
  else r = string_rev s.

Example solve_spec_utf8 :
  solve_spec
    ("тессअমুকলрокअअমুকΑβγুলমlxYMHvkfUুমলа"%string)
    ("ТЕССअমুকলРОКअअমুকαΒΓুলমLXymhVKFuুমলА"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.