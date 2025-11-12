
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (65 <=? n) && (n <=? 90).

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (97 <=? n) && (n <=? 122).

Definition to_upper (c : ascii) : ascii :=
  if is_lower c then
    ascii_of_nat (nat_of_ascii c - 32)
  else c.

Definition to_lower (c : ascii) : ascii :=
  if is_upper c then
    ascii_of_nat (nat_of_ascii c + 32)
  else c.

Definition flip_char_case (c : ascii) : ascii :=
  if is_upper c then to_lower c
  else if is_lower c then to_upper c
  else c.

Fixpoint flip_case_spec (s s' : string) : Prop :=
  match s, s' with
  | EmptyString, EmptyString => True
  | String c cs, String c' cs' =>
      flip_char_case c = c' /\ flip_case_spec cs cs'
  | _, _ => False
  end.
