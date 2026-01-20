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

Fixpoint string_of_bytes (l : list nat) : string :=
  match l with
  | nil => EmptyString
  | n :: tl => String (ascii_of_nat n) (string_of_bytes tl)
  end.

Axiom solve_spec_unicode_case :
  solve_spec
    (string_of_bytes [208;173;195;164;195;171;195;175;195;182;209;128;195;188;209;130;208;190])
    (string_of_bytes [209;141;195;132;195;139;195;143;195;150;208;160;195;156;208;162;208;158]).

Example solve_spec_Unicode :
  solve_spec
    (string_of_bytes [208;173;195;164;195;171;195;175;195;182;209;128;195;188;209;130;208;190])
    (string_of_bytes [209;141;195;132;195;139;195;143;195;150;208;160;195;156;208;162;208;158]).
Proof.
  exact solve_spec_unicode_case.
Qed.