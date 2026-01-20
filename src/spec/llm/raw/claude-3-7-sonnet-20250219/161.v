
Require Import Ascii String.
Open Scope string_scope.

Definition is_letter (c : ascii) : Prop :=
  (("a" <= String c EmptyString)%string /\ (String c EmptyString <= "z")%string) \/
  (("A" <= String c EmptyString)%string /\ (String c EmptyString <= "Z")%string).

Definition swapcase (c : ascii) : ascii :=
  if ("a" <=? c) && (c <=? "z") then Ascii.ascii_of_nat (nat_of_ascii c - 32)
  else if ("A" <=? c) && (c <=? "Z") then Ascii.ascii_of_nat (nat_of_ascii c + 32)
  else c.

Fixpoint forall_letters (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String c rest => is_letter c /\ forall_letters rest
  end.

Fixpoint contains_letter (s : string) : Prop :=
  match s with
  | EmptyString => False
  | String c rest => is_letter c \/ contains_letter rest
  end.

Fixpoint string_reverse (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => string_reverse rest ++ String c EmptyString
  end.

Fixpoint swapcase_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => String (swapcase c) (swapcase_string rest)
  end.

Definition solve_spec (s : string) (result : string) : Prop :=
  (contains_letter s /\ result = swapcase_string s) \/
  (~contains_letter s /\ result = string_reverse s).
