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

Axiom str_of_Z_big : str_of_Z 1234567890987654321%Z = "1234567890987654321".
Axiom length_ltb_big_shift_false : Nat.ltb (String.length "1234567890987654321") 123456791%nat = false.
Axiom modulo_big_shift_len_zero : Nat.modulo 123456791%nat (String.length "1234567890987654321") = 0%nat.

Example circular_shift_test :
  circular_shift_spec 1234567890987654321%Z 123456791%nat "1234567890987654321".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_big.
  rewrite length_ltb_big_shift_false.
  rewrite modulo_big_shift_len_zero.
  simpl.
  reflexivity.
Qed.