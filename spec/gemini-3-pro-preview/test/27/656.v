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
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      let n := nat_of_ascii c in
      if n =? 195 then
        match s' with
        | String c2 s'' =>
            let n2 := nat_of_ascii c2 in
            if (160 <=? n2) && (n2 <=? 191) && (negb (n2 =? 183)) then
              String c (String (ascii_of_nat (n2 - 32)) (flip_case_model s''))
            else if (128 <=? n2) && (n2 <=? 159) && (negb (n2 =? 151)) then
              String c (String (ascii_of_nat (n2 + 32)) (flip_case_model s''))
            else
              String c (String c2 (flip_case_model s''))
        | EmptyString => String c EmptyString
        end
      else
        String (flip_char c) (flip_case_model s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Example test_flip_case_1 : flip_case_spec "¿Habla usted español? Sí, un poco. ¿Habla porítuguésN,," "¿hABLA USTED ESPAÑOL? sÍ, UN POCO. ¿hABLA PORÍTUGUÉSn,,".
Proof.
  unfold flip_case_spec.
  reflexivity.
Qed.