
Require Import String.
Require Import Nat.
Require Import List.

Definition circular_shift_spec (x : nat) (shift : nat) (result : string) : Prop :=
  let s := nat_to_string x in
  let len_s := String.length s in
  if shift >? len_s then
    result = String.rev s
  else
    let shift_mod := shift mod len_s in
    if shift_mod =? 0 then
      result = s
    else
      result = String.append (substring (len_s - shift_mod) len_s s) (substring 0 (len_s - shift_mod) s).
