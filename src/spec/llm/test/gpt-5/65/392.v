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

Axiom str_of_Z_1234567892 : str_of_Z 1234567892%Z = "1234567892".
Axiom reverse_string_1234567892 : reverse_string "1234567892" = "2987654321".
Axiom ltb_len_overshift : Nat.ltb (String.length "1234567892") 1234567890%nat = true.

Example circular_shift_test :
  circular_shift_spec 1234567892%Z 1234567890%nat "2987654321".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_1234567892.
  cbv beta.
  rewrite ltb_len_overshift.
  simpl.
  rewrite reverse_string_1234567892.
  reflexivity.
Qed.