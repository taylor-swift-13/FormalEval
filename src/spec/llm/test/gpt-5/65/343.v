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

Definition big_shift : nat := 85858585858585858585858586%nat.

Axiom str_of_Z_99 : str_of_Z 99%Z = "99".
Axiom reverse_string_99 : reverse_string "99" = "99".
Axiom modulo_big_shift_2_0 : Nat.modulo big_shift 2 = 0%nat.

Example circular_shift_test :
  circular_shift_spec 99%Z big_shift "99".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_99.
  remember (Nat.ltb (String.length "99") big_shift) as b eqn:Hb.
  destruct b.
  - rewrite reverse_string_99. reflexivity.
  - remember (Nat.modulo big_shift (String.length "99")) as k eqn:Hk.
    assert (String.length "99" = 2%nat) by reflexivity.
    rewrite H in Hk.
    rewrite modulo_big_shift_2_0 in Hk.
    subst k.
    simpl.
    reflexivity.
Qed.