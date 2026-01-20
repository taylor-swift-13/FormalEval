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

Axiom str_of_Z_123456789987654320 : str_of_Z 123456789987654320%Z = "123456789987654320".
Axiom reverse_string_123456789987654320 : reverse_string "123456789987654320" = "023456789987654321".
Axiom ltb_len_shift_true :
  let s := str_of_Z 123456789987654320%Z in
  Nat.ltb (String.length s) 123456788%nat = true.

Example circular_shift_test :
  circular_shift_spec 123456789987654320%Z 123456788%nat "023456789987654321".
Proof.
  unfold circular_shift_spec.
  rewrite ltb_len_shift_true.
  simpl.
  rewrite str_of_Z_123456789987654320.
  rewrite reverse_string_123456789987654320.
  reflexivity.
Qed.