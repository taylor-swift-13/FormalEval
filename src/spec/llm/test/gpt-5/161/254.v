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

Definition is_cyr_lead (n : nat) : bool :=
  orb (Nat.eqb n 208) (Nat.eqb n 209).

Fixpoint swapcase_utf8 (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      let n := ascii_code c in
      if is_lower c then String (ascii_of_nat (n - 32)) (swapcase_utf8 s')
      else if is_upper c then String (ascii_of_nat (n + 32)) (swapcase_utf8 s')
      else if is_cyr_lead n then
        match s' with
        | EmptyString => String c EmptyString
        | String d s'' =>
            let m := ascii_code d in
            if Nat.eqb n 208 then
              if andb (Nat.leb 144 m) (Nat.leb m 159) then
                String (ascii_of_nat 208) (String (ascii_of_nat (m + 32)) (swapcase_utf8 s''))
              else if andb (Nat.leb 160 m) (Nat.leb m 175) then
                String (ascii_of_nat 209) (String (ascii_of_nat (m - 32)) (swapcase_utf8 s''))
              else if andb (Nat.leb 176 m) (Nat.leb m 191) then
                String (ascii_of_nat 208) (String (ascii_of_nat (m - 32)) (swapcase_utf8 s''))
              else
                String c (swapcase_utf8 s')
            else
              if andb (Nat.leb 128 m) (Nat.leb m 143) then
                String (ascii_of_nat 208) (String (ascii_of_nat (m + 32)) (swapcase_utf8 s''))
              else
                String c (swapcase_utf8 s')
        end
      else String c (swapcase_utf8 s')
  end.

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter s
  then r = swapcase_utf8 s
  else r = string_rev s.

Example solve_spec_new :
  solve_spec ("احلcحالЭто тестовая строкаاتabc日語def"%string)
             ("احلCحالэТО ТЕСТОВАЯ СТРОКАاتABC日語DEF"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.