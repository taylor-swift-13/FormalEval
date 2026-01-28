Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.

Open Scope string_scope.
Open Scope Z_scope.

(* Concrete definitions for the parameters to allow execution of the test case *)
Definition str_of_Z (z : Z) : string :=
  if Z.eqb z 100 then "100" 
  else if Z.eqb z 789456122 then "789456122"
  else "".

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

Example test_circular_shift : circular_shift_spec 789456122 (Z.to_nat 789456122) "221654987".
Proof.
  (* Make Z.to_nat opaque to prevent simpl from expanding the large number into a unary nat, which would be too slow *)
  Opaque Z.to_nat.
  unfold circular_shift_spec.
  unfold str_of_Z.
  (* Simplify the expression to evaluate the conditionals *)
  replace (Z.eqb 789456122 100) with false by reflexivity.
  replace (Z.eqb 789456122 789456122) with true by reflexivity.
  simpl.
  (* The goal now contains: if Nat.ltb 9 (Z.to_nat 789456122) ... *)
  (* We prove the condition is true using Z arithmetic instead of unary nat arithmetic *)
  assert (H: Nat.ltb 9 (Z.to_nat 789456122) = true).
  {
    apply Nat.ltb_lt.
    apply Z2Nat.inj_lt; try reflexivity.
    (* Prove 9 < 789456122 in Z *)
    reflexivity.
  }
  rewrite H.
  (* The goal simplifies to "221654987" = reverse_string "789456122" *)
  reflexivity.
Qed.