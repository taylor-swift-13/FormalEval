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
  | String c s' => String (flip_char c) (flip_case_model s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Example test_flip_case_new : flip_case_spec "esquIckpКарл у Клары украл кораллы, а К лара у Куарла украла кларнетtThe Quick Brown FOX JUMPμχῃS Over the lazy dogএএটি একটি ণউদাহরণক্t্ত কpমo co.্ষেত্রHeSí,лараañol?" "ESQUiCKPКарл у Клары украл кораллы, а К лара у Куарла украла кларнетTtHE qUICK bROWN fox jumpμχῃs oVER THE LAZY DOGএএটি একটি ণউদাহরণক্T্ত কPমO CO.্ষেত্রhEsí,лараAñOL?".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.