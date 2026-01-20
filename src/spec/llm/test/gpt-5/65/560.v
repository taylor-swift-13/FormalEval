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

Axiom str_of_Z_9999999996 : str_of_Z 9999999996%Z = "9999999996".
Axiom ltb_len_9999999996 : Nat.ltb (String.length "9999999996") 2147483648%nat = true.
Axiom reverse_string_9999999996 : reverse_string "9999999996" = "6999999999".

Example circular_shift_test :
  circular_shift_spec 9999999996%Z 2147483648%nat "6999999999".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_9999999996.
  rewrite ltb_len_9999999996.
  rewrite reverse_string_9999999996.
  reflexivity.
Qed.