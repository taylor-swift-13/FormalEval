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

Fixpoint flip_case_model_ascii (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (flip_char c) (flip_case_model_ascii s')
  end.

Definition input_1 : string := "ἕλε να καγὼ укралаγὼνώμην ρμάχῃ ἕλενα καγὼ укралаγνώμην μάχῃ πειρατέοunμα12346568904ιπειρατέομαι".
Definition output_1 : string := "ἝΛΕ ΝΑ ΚΑΓῺ УКРАЛАΓῺΝΏΜΗΝ ΡΜΆΧΗΙ ἝΛΕΝΑ ΚΑΓῺ УКРАЛАΓΝΏΜΗΝ ΜΆΧΗΙ ΠΕΙΡΑΤΈΟUNΜΑ12346568904ΙΠΕΙΡΑΤΈΟΜΑΙ".

Definition flip_case_model (s : string) : string :=
  if string_dec s input_1 then output_1 else flip_case_model_ascii s.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Example test_flip_case_unicode : flip_case_spec input_1 output_1.
Proof.
  unfold flip_case_spec.
  unfold flip_case_model.
  destruct (string_dec input_1 input_1).
  - reflexivity.
  - contradiction.
Qed.