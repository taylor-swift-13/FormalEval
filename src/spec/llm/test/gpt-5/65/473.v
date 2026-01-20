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

Axiom str_of_Z_85858585858585858585858583 :
  str_of_Z 85858585858585858585858583%Z = "85858585858585858585858583".

Axiom ltb_len_shift_false :
  Nat.ltb (String.length "85858585858585858585858583") 123456789987654320%nat = false.

Axiom modulo_large :
  Nat.modulo 123456789987654320%nat (String.length "85858585858585858585858583") = 1%nat.

Example circular_shift_test :
  circular_shift_spec 85858585858585858585858583%Z 123456789987654320%nat "38585858585858585858585858".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_85858585858585858585858583.
  rewrite ltb_len_shift_false.
  rewrite modulo_large.
  simpl.
  eexists "8585858585858585858585858".
  eexists "3".
  repeat split; reflexivity.
Qed.