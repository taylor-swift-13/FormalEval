Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in (97 <=? n) && (n <=? 122).

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in (65 <=? n) && (n <=? 90).

Definition flip_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if n =? 207 then ascii_of_nat 206
  else if n =? 128 then ascii_of_nat 160
  else if n =? 181 then ascii_of_nat 149
  else if n =? 185 then ascii_of_nat 153
  else if n =? 129 then ascii_of_nat 161
  else if n =? 177 then ascii_of_nat 145
  else if n =? 132 then ascii_of_nat 164
  else if n =? 173 then ascii_of_nat 136
  else if is_lower c then ascii_of_nat (n - 32)
  else if is_upper c then ascii_of_nat (n + 32)
  else c.

Fixpoint flip_case_model (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (flip_char c) (flip_case_model s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Example test_flip_case_unicode : flip_case_spec "πειρατέএটি" "ΠΕΙΡΑΤΈএটি".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.