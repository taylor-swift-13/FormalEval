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

Axiom str_of_Z_10000000003 : str_of_Z 10000000003%Z = "10000000003".
Axiom reverse_string_10000000003 : reverse_string "10000000003" = "30000000001".
Axiom ltb_length_10000000003 : Nat.ltb (String.length "10000000003") 10000000003%nat = true.

Example circular_shift_test :
  circular_shift_spec 10000000003%Z 10000000003%nat "30000000001".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_10000000003.
  rewrite ltb_length_10000000003.
  simpl.
  rewrite reverse_string_10000000003.
  reflexivity.
Qed.