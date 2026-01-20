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

Axiom str_of_Z_2147483647 : str_of_Z 2147483647%Z = "2147483647".

Example circular_shift_test :
  circular_shift_spec 2147483647%Z 6%nat "4836472147".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_2147483647.
  simpl.
  eexists "2147".
  eexists "483647".
  repeat split; reflexivity.
Qed.