Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in (97 <=? n) && (n <=? 122).

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in (65 <=? n) && (n <=? 90).

Definition flip_char_ascii (c : ascii) : ascii :=
  if is_lower c then ascii_of_nat (nat_of_ascii c - 32)
  else if is_upper c then ascii_of_nat (nat_of_ascii c + 32)
  else c.

Fixpoint flip_case_model (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      let n := nat_of_ascii c in
      if (is_lower c || is_upper c) then
        String (flip_char_ascii c) (flip_case_model s')
      else if (n =? 208) then
        match s' with
        | String c2 s'' =>
            let n2 := nat_of_ascii c2 in
            if (144 <=? n2) && (n2 <=? 159) then
               String c (String (ascii_of_nat (n2 + 32)) (flip_case_model s''))
            else if (160 <=? n2) && (n2 <=? 175) then
               String (ascii_of_nat 209) (String (ascii_of_nat (n2 - 32)) (flip_case_model s''))
            else if (176 <=? n2) && (n2 <=? 191) then
               String c (String (ascii_of_nat (n2 - 32)) (flip_case_model s''))
            else
               String c (flip_case_model s')
        | EmptyString => String c EmptyString
        end
      else if (n =? 209) then
        match s' with
        | String c2 s'' =>
            let n2 := nat_of_ascii c2 in
            if (128 <=? n2) && (n2 <=? 143) then
               String (ascii_of_nat 208) (String (ascii_of_nat (n2 + 32)) (flip_case_model s''))
            else
               String c (flip_case_model s')
        | EmptyString => String c EmptyString
        end
      else if (n =? 195) || (n =? 206) then
         match s' with
         | String c2 s'' =>
             let n2 := nat_of_ascii c2 in
             if (160 <=? n2) && (n2 <=? 191) then
                String c (String (ascii_of_nat (n2 - 32)) (flip_case_model s''))
             else if (128 <=? n2) && (n2 <=? 159) then
                String c (String (ascii_of_nat (n2 + 32)) (flip_case_model s''))
             else String c (flip_case_model s')
         | EmptyString => String c EmptyString
         end
      else if (n =? 225) then
          match s' with
          | String c2 (String c3 s''') =>
              if (nat_of_ascii c2 =? 188) && (nat_of_ascii c3 =? 149) then
                  String c (String c2 (String (ascii_of_nat 157) (flip_case_model s''')))
              else if (nat_of_ascii c2 =? 188) && (nat_of_ascii c3 =? 157) then
                  String c (String c2 (String (ascii_of_nat 149) (flip_case_model s''')))
              else String c (flip_case_model s')
          | _ => String c (flip_case_model s')
          end
      else
        String c (flip_case_model s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Example test_flip_case_new : flip_case_spec "Карл  Клары украл кораллы, а Клаb¿Habla usted español? Sí, un poco. ¿Habla portítugués? Não, realmentDOGe no.no.ра у КарлаউদাহরQuickষেত্রἕλενα украла кларнет" "кАРЛ  кЛАРЫ УКРАЛ КОРАЛЛЫ, А кЛАB¿hABLA USTED ESPAÑOL? sÍ, UN POCO. ¿hABLA PORTÍTUGUÉS? nÃO, REALMENTdogE NO.NO.РА У кАРЛАউদাহরqUICKষেত্রἝΛΕΝΑ УКРАЛА КЛАРНЕТ".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.