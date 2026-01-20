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

Axiom str_of_Z_huge :
  str_of_Z 1000000000000000000000000000000000000000%Z
  = "1000000000000000000000000000000000000000".
Axiom reverse_huge :
  reverse_string "1000000000000000000000000000000000000000"
  = "0000000000000000000000000000000000000001".
Axiom ltb_true_huge :
  Nat.ltb (String.length "1000000000000000000000000000000000000000")
          (Z.to_nat 1000000000000000000000000000000000000000%Z) = true.

Example circular_shift_test :
  circular_shift_spec
    1000000000000000000000000000000000000000%Z
    (Z.to_nat 1000000000000000000000000000000000000000%Z)
    "0000000000000000000000000000000000000001".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_huge.
  rewrite ltb_true_huge.
  rewrite reverse_huge.
  reflexivity.
Qed.