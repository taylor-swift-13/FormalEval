Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Open Scope string_scope.

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
  else c.

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (map_string f s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = map_string swap_ascii s.

Example test_flip_case_1 : flip_case_spec "The Quick BrTheown FOX JUMPμ1porvtuguিés?23456789sKaএটিχῃS Over the lazy dogএএটি একটি ণউদাহরণক্t্ত কpমo co.্ষেত্র" "tHE qUICK bRtHEOWN fox jumpμ1PORVTUGUিéS?23456789SkAএটিχῃs oVER THE LAZY DOGএএটি একটি ণউদাহরণক্T্ত কPমO CO.্ষেত্র".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.