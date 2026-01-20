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

Axiom str_of_Z_1234567891 : str_of_Z 1234567891%Z = "1234567891".
Axiom reverse_1234567891 : reverse_string "1234567891" = "1987654321".
Axiom ltb_len_shift_true : Nat.ltb (String.length "1234567891") 1234567892%nat = true.

Example circular_shift_test :
  circular_shift_spec 1234567891%Z 1234567892%nat "1987654321".
Proof.
  unfold circular_shift_spec.
  cbv beta iota.
  rewrite str_of_Z_1234567891.
  rewrite ltb_len_shift_true.
  simpl.
  rewrite reverse_1234567891.
  reflexivity.
Qed.