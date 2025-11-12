
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

Definition check_if_last_char_is_a_letter_spec (txt : string) (result : bool) : Prop :=
  (txt = "" /\ result = false) \/
  (exists c, txt = String c EmptyString /\ result = is_alpha c) \/
  (exists s c1 c2, txt = s ++ String c2 (String c1 EmptyString) /\
                   result = (is_alpha c1 && (c2 = " "))).
