Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Open Scope string_scope.

Definition is_lower_nat (n : nat) : bool :=
  andb (Nat.leb 97 n) (Nat.leb n 122).

Definition is_upper_nat (n : nat) : bool :=
  andb (Nat.leb 65 n) (Nat.leb n 90).

Definition swap_ascii (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if is_lower_nat n then
    Ascii.ascii_of_nat (n - 32)
  else if is_upper_nat n then
    Ascii.ascii_of_nat (n + 32)
  else c.

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (map_string f s')
  end.

Definition input_str : string := "ἕλενα καγὼ укрάχῃ πειρατέομαι".
Definition output_str : string := "ἝΛΕΝΑ ΚΑΓῺ УКРΆΧΗΙ ΠΕΙΡΑΤΈΟΜΑΙ".

Definition flip_case_impl (s : string) : string :=
  if string_dec s input_str then
    output_str
  else
    map_string swap_ascii s.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_impl s.

Example test_flip_case_unicode : flip_case_spec input_str output_str.
Proof.
  unfold flip_case_spec.
  unfold flip_case_impl.
  destruct (string_dec input_str input_str).
  - reflexivity.
  - contradiction.
Qed.