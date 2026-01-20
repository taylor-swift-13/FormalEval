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
  | String c s' => orb (orb (is_alpha c) (negb (Nat.leb (ascii_code c) 127))) (has_letter s')
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
  | [] => EmptyString
  | x :: xs => String (ascii_of_nat x) (string_of_bytes xs)
  end.

Definition emoji_arabic_string : string :=
  string_of_bytes
    [240;159;152;128;240;159;152;130;
     216;167;216;174;216;170;216;170;216;177;216;168;216;177;216;167;216;177;216;167;
     240;159;152;142].

Example solve_spec_emoji_arabic : solve_spec emoji_arabic_string emoji_arabic_string.
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.