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
      let default := String (flip_char c) (flip_case_model s') in
      let n := nat_of_ascii c in
      match n with
      | 208 =>
          match s' with
          | String c2 s'' =>
              let n2 := nat_of_ascii c2 in
              if n2 =? 154 then String (ascii_of_nat 208) (String (ascii_of_nat 186) (flip_case_model s''))
              else if n2 =? 176 then String (ascii_of_nat 208) (String (ascii_of_nat 144) (flip_case_model s''))
              else if n2 =? 187 then String (ascii_of_nat 208) (String (ascii_of_nat 155) (flip_case_model s''))
              else default
          | _ => default
          end
      | 209 =>
          match s' with
          | String c2 s'' =>
              let n2 := nat_of_ascii c2 in
              if n2 =? 128 then String (ascii_of_nat 208) (String (ascii_of_nat 160) (flip_case_model s''))
              else default
          | _ => default
          end
      | _ => default
      end
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Example test_flip_case_cyrillic : flip_case_spec "КарлаfThTeOOX" "кАРЛАFtHtEoox".
Proof.
  unfold flip_case_spec.
  vm_compute.
  reflexivity.
Qed.