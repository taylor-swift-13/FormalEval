
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.

Definition space : ascii := Ascii.ascii_of_nat 32.
Definition hyphen : ascii := Ascii.ascii_of_nat 45.
Definition underscore : ascii := Ascii.ascii_of_nat 95.

Fixpoint repeat_char (c : ascii) (n : nat) : string :=
  match n with
  | 0 => EmptyString
  | S k => String c (repeat_char c k)
  end.

Fixpoint span_spaces (s : string) : nat * string :=
  match s with
  | EmptyString => (0, EmptyString)
  | String a rest =>
      if ascii_dec a space
      then
        let '(n, rest') := span_spaces rest in
        (S n, rest')
      else (0, s)
  end.

Fixpoint span_nonspaces (s : string) : string * string :=
  match s with
  | EmptyString => (EmptyString, EmptyString)
  | String a rest =>
      if ascii_dec a space
      then (EmptyString, s)
      else
        let '(t, rest') := span_nonspaces rest in
        (String a t, rest')
  end.

Fixpoint fix_spaces_compute (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | _ =>
      let '(n, rest1) := span_spaces s in
      match n with
      | 0 =>
          let '(t, rest2) := span_nonspaces s in
          String.append t (fix_spaces_compute rest2)
      | _ =>
          let part :=
            if Nat.leb 3 n
            then String hyphen EmptyString
            else repeat_char underscore n in
          String.append part (fix_spaces_compute rest1)
      end
  end.

Definition fix_spaces_spec (text result : string) : Prop :=
  result = fix_spaces_compute text.
