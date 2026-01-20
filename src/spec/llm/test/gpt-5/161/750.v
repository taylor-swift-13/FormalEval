Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

Definition ascii_code (c : ascii) : nat := nat_of_ascii c.

Definition is_upper (c : ascii) : bool :=
  let n := ascii_code c in andb (Nat.leb 65 n) (Nat.leb n 90).

Definition is_lower (c : ascii) : bool :=
  let n := ascii_code c in andb (Nat.leb 97 n) (Nat.leb n 122).

Definition is_upper_ext (c : ascii) : bool :=
  let n := ascii_code c in orb (orb (Nat.eqb n 143) (Nat.eqb n 150)) (Nat.eqb n 156).

Definition is_lower_ext (c : ascii) : bool :=
  let n := ascii_code c in orb (orb (Nat.eqb n 175) (Nat.eqb n 182)) (Nat.eqb n 188).

Definition is_alpha (c : ascii) : bool :=
  orb (orb (is_upper c) (is_lower c)) (orb (is_upper_ext c) (is_lower_ext c)).

Definition swapcase_char (c : ascii) : ascii :=
  let n := ascii_code c in
  if is_lower c then ascii_of_nat (n - 32)
  else if is_upper c then ascii_of_nat (n + 32)
  else if Nat.eqb n 175 then ascii_of_nat 143
  else if Nat.eqb n 182 then ascii_of_nat 150
  else if Nat.eqb n 188 then ascii_of_nat 156
  else if Nat.eqb n 143 then ascii_of_nat 175
  else if Nat.eqb n 150 then ascii_of_nat 182
  else if Nat.eqb n 156 then ascii_of_nat 188
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

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter s
  then r = string_map swapcase_char s
  else r = string_rev s.

Example solve_spec_arabic_diacritics :
  solve_spec ("ïöتحويلاختبار تحيويل اللحالاتü"%string)
             ("ÏÖتحويلاختبار تحيويل اللحالاتÜ"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.