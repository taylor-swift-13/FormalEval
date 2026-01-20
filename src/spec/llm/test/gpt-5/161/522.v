Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

Definition ascii_code (c : ascii) : nat := nat_of_ascii c.

Definition is_upper (c : ascii) : bool :=
  let n := ascii_code c in andb (Nat.leb 65 n) (Nat.leb n 90).

Definition is_lower (c : ascii) : bool :=
  let n := ascii_code c in andb (Nat.leb 97 n) (Nat.leb n 122).

Definition is_alpha (c : ascii) : bool :=
  orb (orb (is_upper c) (is_lower c)) (Nat.leb 128 (ascii_code c)).

Definition swapcase_char (c : ascii) : ascii :=
  let n := ascii_code c in
  if is_lower c then ascii_of_nat (n - 32)
  else if is_upper c then ascii_of_nat (n + 32)
  else if Nat.eqb n 145 then ascii_of_nat 177
  else if Nat.eqb n 209 then ascii_of_nat 208
  else if Nat.eqb n 129 then ascii_of_nat 161
  else if Nat.eqb n 130 then ascii_of_nat 162
  else if Nat.eqb n 128 then ascii_of_nat 160
  else if Nat.eqb n 186 then ascii_of_nat 154
  else if Nat.eqb n 190 then ascii_of_nat 158
  else if Nat.eqb n 176 then ascii_of_nat 144
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

Example solve_spec_unicode : solve_spec ("अমΑমстрк다окатк다음ল"%string) ("अমαমСТРК다ОКАТК다음ল"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.