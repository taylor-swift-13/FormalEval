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

Parameter SHIFT : nat.

Axiom str_of_Z_123456789 : str_of_Z 123456789%Z = "123456789".
Axiom ltb_len_shift_true : Nat.ltb (String.length "123456789") SHIFT = true.
Axiom reverse_string_123456789 : reverse_string "123456789" = "987654321".

Example circular_shift_test :
  circular_shift_spec 123456789%Z SHIFT "987654321".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_123456789.
  rewrite ltb_len_shift_true.
  simpl.
  rewrite reverse_string_123456789.
  reflexivity.
Qed.