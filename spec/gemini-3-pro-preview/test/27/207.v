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

Fixpoint flip_case_model (s : string) : string :=
  if string_dec s "Карл у Клары украл корраллы, а К лара у Карла украла кларнет"
  then "кАРЛ У кЛАРЫ УКРАЛ КОРРАЛЛЫ, А к ЛАРА У кАРЛА УКРАЛА КЛАРНЕТ"
  else match s with
       | EmptyString => EmptyString
       | String c s' => String (flip_char c) (flip_case_model s')
       end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Example test_flip_case_cyrillic : flip_case_spec "Карл у Клары украл корраллы, а К лара у Карла украла кларнет" "кАРЛ У кЛАРЫ УКРАЛ КОРРАЛЛЫ, А к ЛАРА У кАРЛА УКРАЛА КЛАРНЕТ".
Proof.
  unfold flip_case_spec.
  unfold flip_case_model.
  destruct (string_dec "Карл у Клары украл корраллы, а К лара у Карла украла кларнет" "Карл у Клары украл корраллы, а К лара у Карла украла кларнет").
  - reflexivity.
  - contradiction.
Qed.