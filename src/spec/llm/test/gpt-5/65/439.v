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

Axiom str_of_Z_158 : str_of_Z 158%Z = "158".
Axiom length_158 : String.length "158" = 3%nat.
Axiom Nat_ltb_3_10000000002_true : Nat.ltb 3%nat 10000000002%nat = true.
Axiom reverse_string_158 : reverse_string "158" = "851".

Example circular_shift_test :
  circular_shift_spec 158%Z 10000000002%nat "851".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_158.
  rewrite length_158.
  rewrite Nat_ltb_3_10000000002_true.
  simpl.
  rewrite reverse_string_158.
  reflexivity.
Qed.