Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.

Definition ascii_of_bool (b : bool) : ascii :=
  if b then "1"%char else "0"%char.

Definition bool_of_ascii (c : ascii) : option bool :=
  if ascii_dec c "0"%char then Some false
  else if ascii_dec c "1"%char then Some true
  else None.

Definition xor_ascii (a b : ascii) : option ascii :=
  match bool_of_ascii a, bool_of_ascii b with
  | Some x, Some y => Some (ascii_of_bool (xorb x y))
  | _, _ => None
  end.

Fixpoint string_xor_prefix (a b r : string) : Prop :=
  match a, r with
  | EmptyString, EmptyString => True
  | String ca a', String cr r' =>
      exists cb b',
        b = String cb b' /\
        xor_ascii ca cb = Some cr /\
        string_xor_prefix a' b' r'
  | _, _ => False
  end.

Definition string_xor_spec (a b r : string) : Prop :=
  string_xor_prefix a b r.

Example test_string_xor : string_xor_spec "111000" "101010" "010010".
Proof.
  unfold string_xor_spec.
  simpl.
  exists "1"%char, "01010"%string.
  split. reflexivity.
  split. reflexivity.
  exists "0"%char, "1010"%string.
  split. reflexivity.
  split. reflexivity.
  exists "1"%char, "010"%string.
  split. reflexivity.
  split. reflexivity.
  exists "0"%char, "10"%string.
  split. reflexivity.
  split. reflexivity.
  exists "1"%char, "0"%string.
  split. reflexivity.
  split. reflexivity.
  exists "0"%char, ""%string.
  split. reflexivity.
  split. reflexivity.
  exact I.
Qed.