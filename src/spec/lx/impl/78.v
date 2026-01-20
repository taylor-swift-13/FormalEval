Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Import ListNotations.

Definition is_prime_hex_digit (c : ascii) : bool :=
  match c with "2"%char|"3"%char|"5"%char|"7"%char|"B"%char|"D"%char => true | _ => false end.

Fixpoint count_prime_hex (l : list ascii) : nat :=
  match l with []=>0 | h::t => (if is_prime_hex_digit h then 1 else 0) + count_prime_hex t end.

Definition hex_key_impl (s : list ascii) : nat := count_prime_hex s.

Example hex_key_impl_AB:
  hex_key_impl ("A"%char :: "B"%char :: nil) = 1%nat.
Proof. reflexivity. Qed.

Definition hex_key_spec (s : list ascii) (output : nat) : Prop :=
  output = hex_key_impl s.


