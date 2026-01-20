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

(* We need axioms about str_of_Z for the specific value *)
Axiom str_of_Z_100 : str_of_Z 100 = "100".

Example test_circular_shift : circular_shift_spec 100%Z 2 "001".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_100.
  simpl.
  (* After simpl, we need to show:
     exists u v, "100" = u ++ v /\ String.length v = 2 /\ "001" = v ++ u *)
  exists "1".
  exists "00".
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + reflexivity.
Qed.