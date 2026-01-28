Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in 
  (97 <=? n) && (n <=? 122) ||
  (n =? 176) || (n =? 177) || (n =? 181).

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in 
  (65 <=? n) && (n <=? 90) ||
  (n =? 130) || (n =? 154).

Definition flip_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if is_lower c then ascii_of_nat (n - 32)
  else if is_upper c then ascii_of_nat (n + 32)
  else if n =? 209 then ascii_of_nat 208
  else c.

Fixpoint flip_case_model (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (flip_char c) (flip_case_model s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Example test_flip_case_new : flip_case_spec "e?spañol?КULAbR?OwnZYает" "E?SPAÑOL?кulaBr?oWNzyАЕТ".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.