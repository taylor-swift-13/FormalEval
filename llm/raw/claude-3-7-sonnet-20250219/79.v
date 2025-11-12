
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat.

Definition decimal_to_binary_spec (decimal : N) (result : string) : Prop :=
  exists bin_str : string,
    (forall c : ascii, In c bin_str -> (c = "0"%char \/ c = "1"%char)) /\
    result = String "d"%char (String "b"%char (bin_str ++ String "d"%char (String "b"%char EmptyString))) /\
    N.to_string 2 decimal = bin_str.
