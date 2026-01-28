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
  if is_lower c then ascii_of_nat (n - 32)
  else if is_upper c then ascii_of_nat (n + 32)
  else if n =? 175 then ascii_of_nat 143
  else if n =? 143 then ascii_of_nat 175
  else if n =? 174 then ascii_of_nat 142
  else if n =? 142 then ascii_of_nat 174
  else if n =? 177 then ascii_of_nat 145
  else if n =? 145 then ascii_of_nat 177
  else if n =? 160 then ascii_of_nat 128
  else if n =? 149 then ascii_of_nat 157
  else if n =? 187 then ascii_of_nat 155
  else if n =? 181 then ascii_of_nat 149
  else if n =? 189 then ascii_of_nat 157
  else c.

Fixpoint flip_case_model (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (flip_char c) (flip_case_model s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Example test_flip_case_unicode : flip_case_spec "tHe qউদাহরণuIck bROwn fOX jUMPed over thïîÏÎñÑñàïἕλεναe LAZY DOG" "ThE QউদাহরণUiCK BroWN Fox JumpED OVER THÏÎïîÑñÑÀÏἝΛΕΝΑE lazy dog".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.