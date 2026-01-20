
Require Import String.
Require Import ZArith.
Require Import List.
Import ListNotations.

Definition circular_shift_spec (x : Z) (shift : nat) (result : string) : Prop :=
  let s := Z.to_string x in
  let n := String.length s in
  if Nat.ltb shift n then
    let shift' := Nat.modulo shift n in
    if Nat.eqb shift' 0 then
      result = s
    else
      result = String.append (String.substring (n - shift') shift' s) (String.substring 0 (n - shift') s)
  else
    result = String.rev s.
