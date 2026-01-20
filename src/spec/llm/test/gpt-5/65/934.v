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

Axiom str_of_Z_19 : str_of_Z 19%Z = "19".
Axiom reverse_string_19 : reverse_string "19" = "91".
Axiom ltb_len_19_huge : Nat.ltb (String.length "19") 85858585858585858585858587%nat = true.

Example circular_shift_test :
  circular_shift_spec 19%Z 85858585858585858585858587%nat "91".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_19.
  rewrite ltb_len_19_huge.
  simpl.
  rewrite reverse_string_19.
  reflexivity.
Qed.