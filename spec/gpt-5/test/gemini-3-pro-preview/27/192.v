Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Open Scope string_scope.

Definition is_lower_nat (n : nat) : bool :=
  orb (andb (Nat.leb 97 n) (Nat.leb n 122))
      (andb (Nat.leb 176 n) (Nat.leb n 191)).

Definition is_upper_nat (n : nat) : bool :=
  orb (andb (Nat.leb 65 n) (Nat.leb n 90))
      (andb (Nat.leb 128 n) (Nat.leb n 143)).

Definition swap_ascii (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if is_lower_nat n then
    Ascii.ascii_of_nat (n - 32)
  else if is_upper_nat n then
    Ascii.ascii_of_nat (n + 32)
  else if Nat.eqb n 209 then
    Ascii.ascii_of_nat 208
  else c.

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (map_string f s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = map_string swap_ascii s.

Example test_flip_case_cyrillic : flip_case_spec "12украалуа34567890" "12УКРААЛУА34567890".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.