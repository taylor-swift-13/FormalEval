
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Definition encrypt_spec (s : string) (encrypted_s : string) : Prop :=
  let d := "abcdefghijklmnopqrstuvwxyz" in
  let rotate (ch : ascii) : ascii :=
    if existsb (fun x => x =? ch) (list_ascii_of_string d)
    then ascii_of_nat (((nat_of_ascii ch - nat_of_ascii "a" + 4) mod 26) + nat_of_ascii "a")
    else ch
  in
  encrypted_s = string_of_list_ascii (map rotate (list_ascii_of_string s)).
