Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

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
  | String c s' => String (flip_char c) (flip_case_model s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Fixpoint string_of_bytes (l : list nat) : string :=
  match l with
  | [] => EmptyString
  | n :: l' => String (ascii_of_nat n) (string_of_bytes l')
  end.

Definition test_input_bytes : list nat := [
  195; 175; 195; 174; 195; 143; 195; 142; 195; 177; 195; 145; 195; 177; 195; 160; 195; 175;
  225; 188; 149; 206; 187; 206; 181; 206; 189; 206; 177; 32;
  206; 186; 206; 177; 206; 179; 225; 189; 176; 32;
  209; 131; 208; 186; 209; 128; 208; 176; 208; 187; 208; 176; 206; 179; 206; 189; 208; 176; 207; 142; 206; 188; 206; 183; 206; 189; 32;
  206; 188; 206; 172; 207; 131; 225; 191; 131; 32;
  207; 128; 206; 181; 206; 185; 207; 129; 206; 177; 207; 132; 206; 173; 206; 191; 206; 188; 206; 177; 206; 185;
  195; 128; 195; 161; 195; 129; 195; 169; 195; 137; 195; 141; 195; 178; 195; 146; 195; 186; 195; 153; 195; 188; 195; 156
].

Definition test_input : string := string_of_bytes test_input_bytes.

Example test_flip_case_unicode : flip_case_spec test_input test_input.
Proof.
  unfold flip_case_spec.
  reflexivity.
Qed.