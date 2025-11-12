
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Bool.Bool.

Definition change_base_spec (x : nat) (base : nat) (result : string) : Prop :=
  base < 10 /\
  (x = 0 -> result = "0") /\
  (x <> 0 ->
   exists digits : list nat,
     (forall d, In d digits -> d < base) /\
     fold_left (fun acc d => acc * base + d) digits 0 = x /\
     result = fold_right (fun d acc => String (ascii_of_nat (48 + d)) acc) "" digits).
