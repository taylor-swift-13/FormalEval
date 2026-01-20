
Require Import String Ascii List.

Definition encode_shift_spec (s : string) (encoded : string) : Prop :=
  encoded = String.concat "" (map (fun ch => ascii_of_nat (((nat_of_ascii ch + 5 - nat_of_ascii "a") mod 26) + nat_of_ascii "a")) (list_ascii_of_string s)).

Definition decode_shift_spec (s : string) (decoded : string) : Prop :=
  decoded = String.concat "" (map (fun ch => ascii_of_nat (((nat_of_ascii ch - nat_of_ascii "a" - 5 + 26) mod 26) + nat_of_ascii "a")) (list_ascii_of_string s)).
