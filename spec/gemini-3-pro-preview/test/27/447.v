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
      match n with
      | 195 => 
          match s' with
          | String c2 s'' =>
              if nat_of_ascii c2 =? 169 then
                 String (ascii_of_nat 195) (String (ascii_of_nat 137) (flip_case_model s''))
              else String (flip_char c) (flip_case_model s')
          | EmptyString => String (flip_char c) EmptyString
          end
      | 209 => 
          match s' with
          | String c2 s'' =>
             match nat_of_ascii c2 with
             | 131 => String (ascii_of_nat 208) (String (ascii_of_nat 163) (flip_case_model s''))
             | 128 => String (ascii_of_nat 208) (String (ascii_of_nat 160) (flip_case_model s''))
             | _ => String (flip_char c) (flip_case_model s')
             end
          | EmptyString => String (flip_char c) EmptyString
          end
      | 208 => 
          match s' with
          | String c2 s'' =>
             match nat_of_ascii c2 with
             | 186 => String (ascii_of_nat 208) (String (ascii_of_nat 154) (flip_case_model s''))
             | 176 => String (ascii_of_nat 208) (String (ascii_of_nat 144) (flip_case_model s''))
             | 187 => String (ascii_of_nat 208) (String (ascii_of_nat 155) (flip_case_model s''))
             | _ => String (flip_char c) (flip_case_model s')
             end
          | EmptyString => String (flip_char c) EmptyString
          end
      | _ => String (flip_char c) (flip_case_model s')
      end
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Example test_flip_case_new : flip_case_spec "1portugués?23456789sKaএটি একটি portugués?укруалаQuicণউদাহরণক্্তণউদাহরণক্্ত কpমoco.্ষেত্রwvm0একটএি" "1PORTUGUÉS?23456789SkAএটি একটি PORTUGUÉS?УКРУАЛАqUICণউদাহরণক্্তণউদাহরণক্্ত কPমOCO.্ষেত্রWVM0একটএি".
Proof.
  unfold flip_case_spec.
  reflexivity.
Qed.