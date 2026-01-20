Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.

Local Open Scope string_scope.

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

Fixpoint chunk4_strings (s : string) : list string :=
  match s with
  | String a1 (String a2 (String a3 (String a4 rest))) =>
      (String a1 (String a2 (String a3 (String a4 EmptyString)))) :: chunk4_strings rest
  | _ => nil
  end.

Fixpoint concat_strings (l : list string) : string :=
  match l with
  | nil => EmptyString
  | s1 :: tl => s1 ++ concat_strings tl
  end.

Definition string_rev_utf8_quads (s : string) : string :=
  concat_strings (List.rev (chunk4_strings s)).

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter s
  then r = string_map swapcase_char s
  else r = string_rev_utf8_quads s.

Example solve_spec_emojis : solve_spec ("😎😀😀😂😂😎"%string) ("😎😂😂😀😀😎"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.