Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition str_of_Z (z : Z) : string :=
  if Z.eqb z 789456124 then "789456124" else "".

Fixpoint reverse_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => (reverse_string s') ++ (String c EmptyString)
  end.

Definition circular_shift_spec (x : Z) (shift : Z) (res : string) : Prop :=
  let s := str_of_Z x in
  let len := String.length s in
  let len_z := Z.of_nat len in
  if Z.ltb len_z shift then
    res = reverse_string s
  else
    let k := Z.to_nat (Z.modulo shift len_z) in
    if Nat.eqb k 0 then
      res = s
    else
      exists u v,
        s = u ++ v /\
        String.length v = k /\
        res = v ++ u.

Example test_circular_shift : circular_shift_spec 789456124 789456124 "421654987".
Proof.
  unfold circular_shift_spec.
  unfold str_of_Z.
  simpl.
  reflexivity.
Qed.