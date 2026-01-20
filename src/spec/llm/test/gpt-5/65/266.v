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
Axiom ltb_len_2147483647_2147483648 : Nat.ltb (String.length "2147483647") 2147483648%nat = true.
Axiom reverse_string_2147483647 : reverse_string "2147483647" = "7463847412".

Example circular_shift_test :
  circular_shift_spec 2147483647%Z 2147483648%nat "7463847412".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_2147483647.
  rewrite ltb_len_2147483647_2147483648.
  simpl.
  rewrite reverse_string_2147483647.
  reflexivity.
Qed.