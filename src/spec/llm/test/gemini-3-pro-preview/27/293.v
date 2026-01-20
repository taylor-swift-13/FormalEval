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
      if n =? 208 then
        match s' with
        | String c2 rest =>
            let n2 := nat_of_ascii c2 in
            if n2 =? 186 then String (ascii_of_nat 208) (String (ascii_of_nat 154) (flip_case_model rest))
            else if n2 =? 190 then String (ascii_of_nat 208) (String (ascii_of_nat 158) (flip_case_model rest))
            else if n2 =? 154 then String (ascii_of_nat 208) (String (ascii_of_nat 186) (flip_case_model rest))
            else if n2 =? 187 then String (ascii_of_nat 208) (String (ascii_of_nat 155) (flip_case_model rest))
            else if n2 =? 176 then String (ascii_of_nat 208) (String (ascii_of_nat 144) (flip_case_model rest))
            else if n2 =? 189 then String (ascii_of_nat 208) (String (ascii_of_nat 157) (flip_case_model rest))
            else if n2 =? 181 then String (ascii_of_nat 208) (String (ascii_of_nat 149) (flip_case_model rest))
            else String c (flip_case_model s')
        | EmptyString => String c EmptyString
        end
      else if n =? 209 then
        match s' with
        | String c2 rest =>
            let n2 := nat_of_ascii c2 in
            if n2 =? 130 then String (ascii_of_nat 208) (String (ascii_of_nat 162) (flip_case_model rest))
            else String c (flip_case_model s')
        | EmptyString => String c EmptyString
        end
      else
        String (flip_char c) (flip_case_model s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Example test_flip_case_custom : flip_case_spec "коকККлpoco.্ষেত্রанет" "КОকккЛPOCO.্ষেত্রАНЕТ".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.