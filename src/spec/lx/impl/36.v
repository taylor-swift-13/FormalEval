Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.

Fixpoint count_digit_7_aux (k fuel:nat) : nat :=
  match fuel with 0=>0 | S f' => match k with 0=>0 | _ => (if Nat.eqb (k mod 10) 7 then 1 else 0) + count_digit_7_aux (k/10) f' end end.
Definition count_digit_7 (k:nat) : nat := count_digit_7_aux k k.

Definition fizz_buzz_impl (n:nat) : nat :=
  List.fold_left (fun acc i => acc + (if orb (Nat.eqb (i mod 11) 0) (Nat.eqb (i mod 13) 0) then count_digit_7 i else 0)) (List.seq 0 n) 0.

Example fizz_buzz_impl_78: fizz_buzz_impl 78%nat = 2%nat.
Proof. reflexivity. Qed.

Definition fizz_buzz_spec (n : nat) (output : nat) : Prop :=
  output = fizz_buzz_impl n.


