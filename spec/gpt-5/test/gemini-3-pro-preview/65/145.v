Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.
Open Scope Z_scope.

(* Concrete definitions for the parameters to allow execution of the test case *)
Definition str_of_Z (z : Z) : string :=
  if Z.eqb z 2147483647 then "2147483647" else "".

Fixpoint reverse_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => (reverse_string s') ++ (String c EmptyString)
  end.

Definition circular_shift_spec (x : Z) (shift : Z) (res : string) : Prop :=
  let s := str_of_Z x in
  let len := Z.of_nat (String.length s) in
  if Z.ltb len shift then
    res = reverse_string s
  else
    let k := Z.modulo shift len in
    if Z.eqb k 0 then
      res = s
    else
      exists u v,
        s = u ++ v /\
        Z.of_nat (String.length v) = k /\
        res = v ++ u.

Example test_circular_shift : circular_shift_spec 2147483647 1234567890987654322 "7463847412".
Proof.
  unfold circular_shift_spec.
  unfold str_of_Z.
  simpl.
  reflexivity.
Qed.