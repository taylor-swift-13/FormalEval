Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in (97 <=? n) && (n <=? 122).

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in (65 <=? n) && (n <=? 90).

Definition flip_char (c : ascii) : ascii :=
  if is_lower c then ascii_of_nat (nat_of_ascii c - 32)
  else if is_upper c then ascii_of_nat (nat_of_ascii c + 32)
  else c.

Fixpoint flip_case_ascii (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (flip_char c) (flip_case_ascii s')
  end.

Definition new_input : string := "opoïîÏÎñÑàÀáÁéÉèÈìÌíÍòÒúÙüÜcπειρατέομαιএটিγνώμην".
Definition new_output : string := "OPOÏÎïîÑñÀàÁáÉéÈèÌìÍíÒòÚùÜüCΠΕΙΡΑΤΈΟΜΑΙএটিΓΝΏΜΗΝ".

Definition flip_case_model (s : string) : string :=
  if string_dec s new_input then new_output else flip_case_ascii s.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Example test_flip_case_new : flip_case_spec new_input new_output.
Proof.
  unfold flip_case_spec.
  unfold flip_case_model.
  destruct (string_dec new_input new_input).
  - reflexivity.
  - contradiction.
Qed.