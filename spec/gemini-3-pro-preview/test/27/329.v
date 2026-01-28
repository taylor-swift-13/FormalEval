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
  | String c s' =>
      let n := nat_of_ascii c in
      if (n =? 208) then (* UTF-8 Lead byte D0 *)
        match s' with
        | String c2 s'' =>
            let n2 := nat_of_ascii c2 in
            (* Upper A-Pe (90-9F) -> Lower a-pe (B0-BF) *)
            if (144 <=? n2) && (n2 <=? 159) then
              String c (String (ascii_of_nat (n2 + 32)) (flip_case_model s''))
            (* Lower a-pe (B0-BF) -> Upper A-Pe (90-9F) *)
            else if (176 <=? n2) && (n2 <=? 191) then
              String c (String (ascii_of_nat (n2 - 32)) (flip_case_model s''))
            (* Upper Er-Ya (A0-AF) -> Lower er-ya (D1 80-8F) *)
            else if (160 <=? n2) && (n2 <=? 175) then
              String (ascii_of_nat 209) (String (ascii_of_nat (n2 - 32)) (flip_case_model s''))
            else
              String c (flip_case_model s')
        | EmptyString => String c EmptyString
        end
      else if (n =? 209) then (* UTF-8 Lead byte D1 *)
        match s' with
        | String c2 s'' =>
            let n2 := nat_of_ascii c2 in
            (* Lower er-ya (80-8F) -> Upper Er-Ya (D0 A0-AF) *)
            if (128 <=? n2) && (n2 <=? 143) then
              String (ascii_of_nat 208) (String (ascii_of_nat (n2 + 32)) (flip_case_model s''))
            else
              String c (flip_case_model s')
        | EmptyString => String c EmptyString
        end
      else
        (* ASCII logic *)
        String (flip_char c) (flip_case_model s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Fixpoint string_of_bytes (l : list nat) : string :=
  match l with
  | [] => EmptyString
  | n :: l' => String (ascii_of_nat n) (string_of_bytes l')
  end.

Definition input_bytes : list nat := [
  208; 154; 208; 176; 209; 128; 208; 187; 32; 209; 131; 32; 208; 176; 208; 154; 
  208; 187; 208; 176; 209; 128; 209; 139; 32; 209; 131; 208; 186; 209; 128; 208; 
  176; 208; 187; 32; 208; 186; 208; 190; 209; 128; 208; 176; 208; 187; 208; 187; 
  209; 139; 44; 32; 208; 176; 32; 208; 154; 208; 187; 208; 176; 209; 128; 208; 
  176; 32; 209; 131; 32; 208; 154; 208; 176; 209; 128; 208; 187; 208; 176; 209; 
  139; 32; 209; 131; 208; 186; 209; 128; 208; 176; 208; 187; 208; 176; 32; 208; 
  186; 208; 187; 208; 176; 208; 189; 208; 181; 209; 130
].

Definition output_bytes : list nat := [
  208; 186; 208; 144; 208; 160; 208; 155; 32; 208; 163; 32; 208; 144; 208; 186; 
  208; 155; 208; 144; 208; 160; 208; 171; 32; 208; 163; 208; 154; 208; 160; 208; 
  144; 208; 155; 32; 208; 154; 208; 158; 208; 160; 208; 144; 208; 155; 208; 155; 
  208; 171; 44; 32; 208; 144; 32; 208; 186; 208; 155; 208; 144; 208; 160; 208; 
  144; 32; 208; 163; 32; 208; 186; 208; 144; 208; 160; 208; 155; 208; 144; 208; 
  171; 32; 208; 163; 208; 154; 208; 160; 208; 144; 208; 155; 208; 144; 32; 208; 
  154; 208; 155; 208; 144; 208; 157; 208; 149; 208; 162
].

Example test_flip_case_cyrillic : flip_case_spec (string_of_bytes input_bytes) (string_of_bytes output_bytes).
Proof.
  unfold flip_case_spec.
  vm_compute.
  reflexivity.
Qed.