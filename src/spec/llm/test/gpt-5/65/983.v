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

Axiom str_of_Z_198 : str_of_Z 198%Z = "198".
Axiom str_len_198 : String.length "198" = 3.
Axiom ltb_3_10000000001 : Nat.ltb 3 10000000001%nat = true.
Axiom reverse_string_198 : reverse_string "198" = "891".

Example circular_shift_test :
  circular_shift_spec 198%Z 10000000001%nat "891".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_198.
  rewrite str_len_198.
  rewrite ltb_3_10000000001.
  simpl.
  rewrite reverse_string_198.
  reflexivity.
Qed.