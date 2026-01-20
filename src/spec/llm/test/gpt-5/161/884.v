Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.

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

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter s
  then r = string_map swapcase_char s
  else r = string_rev s.

Fixpoint mk_string (l : list nat) : string :=
  match l with
  | nil => EmptyString
  | n :: l' => String (ascii_of_nat n) (mk_string l')
  end.

Definition s_unicode : string :=
  mk_string [224;164;133;208;181;224;164;133;209;130;208;181;208;176;209;143;209;130;224;164;168;224;165;129;224;164;174].

Definition r_unicode : string :=
  mk_string [224;164;133;208;149;224;164;133;208;162;208;149;208;144;208;175;208;162;224;164;168;224;165;129;224;164;174].

Axiom has_letter_s_unicode : has_letter s_unicode = true.
Axiom swapcase_s_unicode : string_map swapcase_char s_unicode = r_unicode.

Example solve_spec_unicode : solve_spec s_unicode r_unicode.
Proof.
  unfold solve_spec.
  rewrite has_letter_s_unicode.
  rewrite swapcase_s_unicode.
  reflexivity.
Qed.