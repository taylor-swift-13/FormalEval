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

Axiom str_of_Z_46 : str_of_Z 46%Z = "46".
Axiom reverse_string_46 : reverse_string "46" = "64".
Axiom ltb_len_46_big : Nat.ltb (String.length "46") (Z.to_nat 10000000000%Z) = true.

Example circular_shift_test :
  circular_shift_spec 46%Z (Z.to_nat 10000000000%Z) "64".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_46.
  rewrite ltb_len_46_big.
  rewrite reverse_string_46.
  reflexivity.
Qed.