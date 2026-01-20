Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Local Open Scope string_scope.

Definition is_lower_nat (n : nat) : bool :=
  orb (andb (Nat.leb 97 n) (Nat.leb n 122))
      (andb (Nat.leb 224 n) (Nat.leb n 255)).

Definition is_upper_nat (n : nat) : bool :=
  orb (andb (Nat.leb 65 n) (Nat.leb n 90))
      (andb (Nat.leb 192 n) (Nat.leb n 222)).

Definition swap_ascii (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if is_lower_nat n then
    Ascii.ascii_of_nat (n - 32)
  else if is_upper_nat n then
    Ascii.ascii_of_nat (n + 32)
  else c.

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (map_string f s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = map_string swap_ascii s.

Example flip_case_SiS:
  flip_case_spec
    (String (Ascii.ascii_of_nat 83)
      (String (Ascii.ascii_of_nat 237)
        (String (Ascii.ascii_of_nat 83)
          (String (Ascii.ascii_of_nat 44) EmptyString))))
    (String (Ascii.ascii_of_nat 115)
      (String (Ascii.ascii_of_nat 205)
        (String (Ascii.ascii_of_nat 115)
          (String (Ascii.ascii_of_nat 44) EmptyString)))).
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.