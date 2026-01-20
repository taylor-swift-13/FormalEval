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

Axiom str_of_Z_123456788 : str_of_Z 123456788%Z = "123456788".
Axiom ltb_len_large : Nat.ltb (String.length "123456788") (Z.to_nat 1234567890987654322%Z) = true.
Axiom reverse_123456788 : reverse_string "123456788" = "887654321".

Example circular_shift_test :
  circular_shift_spec 123456788%Z (Z.to_nat 1234567890987654322%Z) "887654321".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_123456788.
  rewrite ltb_len_large.
  rewrite reverse_123456788.
  reflexivity.
Qed.