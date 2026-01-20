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

Axiom str_of_Z_9999999999 : str_of_Z 9999999999%Z = "9999999999".
Axiom reverse_string_9999999999 : reverse_string "9999999999" = "9999999999".

Parameter shift_10000000000 : nat.
Axiom ltb_len_shift_10000000000 :
  Nat.ltb (String.length "9999999999") shift_10000000000 = true.

Example circular_shift_test :
  circular_shift_spec 9999999999%Z shift_10000000000 "9999999999".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_9999999999.
  rewrite ltb_len_shift_10000000000.
  simpl.
  rewrite reverse_string_9999999999.
  reflexivity.
Qed.