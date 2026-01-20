Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.

Parameter str_of_Z : Z -> string.
Parameter reverse_string : string -> string.

Definition circular_shift_spec (x : Z) (shift : nat) (res : string) : Prop :=
  let s := str_of_Z x in
  if Nat.ltb (String.length s) shift then
    res = reverse_string s
  else
    let k := Nat.modulo shift (String.length s) in
    if Nat.eqb k 0 then
      res = s
    else
      exists u v,
        s = u ++ v /\
        String.length v = k /\
        res = v ++ u.

Axiom str_of_Z_14 : str_of_Z 14%Z = "14".
Axiom reverse_string_14 : reverse_string "14" = "41".

Example circular_shift_test :
  circular_shift_spec 14%Z 13%nat "41".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_14.
  simpl.
  rewrite reverse_string_14.
  reflexivity.
Qed.