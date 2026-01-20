
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Local OpenScope string_scope.
Local OpenScope Z_scope.

(* Assuming a function that converts an integer to its string representation *)
Parameter Z_to_string : Z -> string.

Fixpoint string_rev (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => (string_rev s') ++ (String c EmptyString)
  end.

Definition circular_shift_spec (x : Z) (shift : nat) (result : string) : Prop :=
  let s := Z_to_string x in
  let n := String.length s in
  if (n <? shift)%nat then
    result = string_rev s
  else
    let k := (shift mod n)%nat in
    if (k =? 0)%nat then
      result = s
    else
      result = (substring (n - k) k s) ++ (substring 0 (n - k) s).
