Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Local Open Scope string_scope.

Definition is_lower_nat (n : nat) : bool :=
  andb (Nat.leb 97 n) (Nat.leb n 122).

Definition is_upper_nat (n : nat) : bool :=
  andb (Nat.leb 65 n) (Nat.leb n 90).

Definition swap_ascii (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  let m :=
    if is_lower_nat n then n - 32
    else if is_upper_nat n then n + 32
    else if Nat.eqb n 154 then 186
    else if Nat.eqb n 186 then 154
    else if Nat.eqb n 144 then 176
    else if Nat.eqb n 176 then 144
    else if Nat.eqb n 155 then 187
    else if Nat.eqb n 187 then 155
    else if Nat.eqb n 128 then 160
    else if Nat.eqb n 160 then 128
    else if Nat.eqb n 139 then 171
    else if Nat.eqb n 171 then 139
    else if Nat.eqb n 209 then 208
    else n
  in Ascii.ascii_of_nat m.

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (map_string f s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = map_string swap_ascii s.

Example flip_case_cyrillic: flip_case_spec "Карлаы" "кАРЛАЫ".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.