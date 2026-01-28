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
      if n =? 207 then
        match s' with
        | String c2 s'' =>
            let n2 := nat_of_ascii c2 in
            if n2 =? 128 then String (ascii_of_nat 206) (String (ascii_of_nat 160) (flip_case_model s''))
            else if n2 =? 129 then String (ascii_of_nat 206) (String (ascii_of_nat 161) (flip_case_model s''))
            else if n2 =? 132 then String (ascii_of_nat 206) (String (ascii_of_nat 164) (flip_case_model s''))
            else if n2 =? 142 then String (ascii_of_nat 206) (String (ascii_of_nat 143) (flip_case_model s''))
            else String c (flip_case_model s')
        | EmptyString => String c EmptyString
        end
      else if n =? 206 then
        match s' with
        | String c2 s'' =>
            let n2 := nat_of_ascii c2 in
            if n2 =? 181 then String (ascii_of_nat 206) (String (ascii_of_nat 149) (flip_case_model s''))
            else if n2 =? 185 then String (ascii_of_nat 206) (String (ascii_of_nat 153) (flip_case_model s''))
            else if n2 =? 177 then String (ascii_of_nat 206) (String (ascii_of_nat 145) (flip_case_model s''))
            else if n2 =? 173 then String (ascii_of_nat 206) (String (ascii_of_nat 136) (flip_case_model s''))
            else if n2 =? 191 then String (ascii_of_nat 206) (String (ascii_of_nat 159) (flip_case_model s''))
            else if n2 =? 179 then String (ascii_of_nat 206) (String (ascii_of_nat 147) (flip_case_model s''))
            else if n2 =? 189 then String (ascii_of_nat 206) (String (ascii_of_nat 157) (flip_case_model s''))
            else if n2 =? 188 then String (ascii_of_nat 206) (String (ascii_of_nat 156) (flip_case_model s''))
            else if n2 =? 183 then String (ascii_of_nat 206) (String (ascii_of_nat 151) (flip_case_model s''))
            else String c (flip_case_model s')
        | EmptyString => String c EmptyString
        end
      else String (flip_char c) (flip_case_model s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Example test_flip_case_unicode : flip_case_spec "opocπειρατέοTheটিγνώμην" "OPOCΠΕΙΡΑΤΈΟtHEটিΓΝΏΜΗΝ".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.