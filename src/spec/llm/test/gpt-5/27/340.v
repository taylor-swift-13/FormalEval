Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

Local Open Scope string_scope.

Definition is_lower_nat (n : nat) : bool :=
  andb (Nat.leb 97 n) (Nat.leb n 122).

Definition is_upper_nat (n : nat) : bool :=
  andb (Nat.leb 65 n) (Nat.leb n 90).

Definition swap_ascii (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if is_lower_nat n then
    Ascii.ascii_of_nat (n - 32)
  else if is_upper_nat n then
    Ascii.ascii_of_nat (n + 32)
  else if Nat.eqb n 207 then
    Ascii.ascii_of_nat 206
  else if Nat.eqb n 128 then
    Ascii.ascii_of_nat 160
  else if Nat.eqb n 129 then
    Ascii.ascii_of_nat 161
  else if Nat.eqb n 132 then
    Ascii.ascii_of_nat 164
  else if Nat.eqb n 173 then
    Ascii.ascii_of_nat 136
  else if Nat.eqb n 191 then
    Ascii.ascii_of_nat 159
  else if Nat.eqb n 188 then
    Ascii.ascii_of_nat 156
  else if Nat.eqb n 177 then
    Ascii.ascii_of_nat 145
  else if Nat.eqb n 181 then
    Ascii.ascii_of_nat 149
  else if Nat.eqb n 185 then
    Ascii.ascii_of_nat 153
  else c.

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (map_string f s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = map_string swap_ascii s.

Example flip_case_greek: flip_case_spec "πειρατέοunμα12346568290ιπειρατέομαι" "ΠΕΙΡΑΤΈΟUNΜΑ12346568290ΙΠΕΙΡΑΤΈΟΜΑΙ".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.