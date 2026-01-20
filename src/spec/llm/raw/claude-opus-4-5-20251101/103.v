
Require Import ZArith.
Require Import String.
Require Import Ascii.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

Definition round_half_up (x : Z) (y : Z) : Z :=
  let q := x / y in
  let r := x mod y in
  if (2 * r >=? y) then q + 1 else q.

Fixpoint to_binary_aux (n : nat) (z : Z) : string :=
  match n with
  | O => ""
  | S n' =>
    if z <=? 0 then ""
    else
      let bit := if (z mod 2 =? 1) then "1" else "0" in
      append (to_binary_aux n' (z / 2)) bit
  end.

Definition to_binary (z : Z) : string :=
  if z =? 0 then "0b0"
  else append "0b" (to_binary_aux (Z.to_nat z + 1) z).

Inductive result : Type :=
  | Error : result
  | Binary : string -> result.

Definition rounded_avg_spec (n m : Z) (res : result) : Prop :=
  (n > m -> res = Error) /\
  (n <= m -> 
    let sum := n + m in
    let avg := round_half_up sum 2 in
    res = Binary (to_binary avg)).
