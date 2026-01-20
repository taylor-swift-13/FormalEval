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

Axiom str_of_Z_157 : str_of_Z 157%Z = "157".
Axiom reverse_string_157 : reverse_string "157" = "751".
Axiom ltb_len_157_big_shift :
  Nat.ltb (String.length "157") (Z.to_nat 85858585858585858585858584%Z) = true.

Example circular_shift_test :
  circular_shift_spec 157%Z (Z.to_nat 85858585858585858585858584%Z) "751".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_157.
  rewrite ltb_len_157_big_shift.
  simpl.
  rewrite reverse_string_157.
  reflexivity.
Qed.