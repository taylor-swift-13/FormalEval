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

Axiom str_of_Z_9999999998 : str_of_Z 9999999998%Z = "9999999998".
Axiom reverse_string_9999999998 : reverse_string "9999999998" = "8999999999".
Axiom ltb_len_9999999998_1234567890 : Nat.ltb (String.length "9999999998") 1234567890%nat = true.

Example circular_shift_test :
  circular_shift_spec 9999999998%Z 1234567890%nat "8999999999".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_9999999998.
  rewrite ltb_len_9999999998_1234567890.
  simpl.
  rewrite reverse_string_9999999998.
  reflexivity.
Qed.