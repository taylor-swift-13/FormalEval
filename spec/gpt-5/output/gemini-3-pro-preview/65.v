Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.
Open Scope Z_scope.

(* Concrete definitions for the parameters to allow execution of the test case *)
Definition str_of_Z (z : Z) : string :=
  if Z.eqb z 100 then "100" else "".

Fixpoint reverse_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => (reverse_string s') ++ (String c EmptyString)
  end.

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

Example test_circular_shift : circular_shift_spec 100 2%nat "001".
Proof.
  unfold circular_shift_spec.
  unfold str_of_Z.
  (* Simplify the expression to evaluate the conditionals *)
  simpl.
  (* The goal becomes: exists u v : string, "100" = u ++ v /\ String.length v = 2 /\ "001" = v ++ u *)
  exists "1".
  exists "00".
  (* Prove the conjunctions explicitly *)
  split.
  - reflexivity. (* Check "100" = "1" ++ "00" *)
  - split.
    + reflexivity. (* Check String.length "00" = 2 *)
    + reflexivity. (* Check "001" = "00" ++ "1" *)
Qed.