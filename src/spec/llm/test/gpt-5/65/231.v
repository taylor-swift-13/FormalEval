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

Axiom str_of_Z_999 : str_of_Z 999%Z = "999".
Axiom reverse_string_999 : reverse_string "999" = "999".

Example circular_shift_test :
  circular_shift_spec 999%Z 2147483646%nat "999".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_999.
  simpl.
  rewrite reverse_string_999.
  reflexivity.
Qed.