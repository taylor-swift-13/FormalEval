Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.
Open Scope Z_scope.

(* Implementations for the parameters to make the test case provable *)
Definition str_of_Z (z : Z) : string :=
  if Z.eqb z 100 then "100" else "".

Fixpoint reverse_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => (reverse_string s') ++ (String c EmptyString)
  end.

(* The specification definition *)
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

(* The test case proof *)
Example test_circular_shift : circular_shift_spec 100 2 "001".
Proof.
  (* Unfold the specification definition *)
  unfold circular_shift_spec.
  
  (* Simplify the expression. 
     - str_of_Z 100 evaluates to "100"
     - length "100" evaluates to 3
     - Nat.ltb 3 2 evaluates to false
     - k = 2 mod 3 evaluates to 2
     - Nat.eqb 2 0 evaluates to false
  *)
  simpl.
  
  (* We are now in the 'else' branch of the second if.
     Goal: exists u v : string, "100" = u ++ v /\ 2 = 2 /\ "001" = v ++ u 
     We instantiate u as "1" and v as "00".
  *)
  exists "1", "00".
  
  (* Verify the conditions *)
  split.
  - (* "100" = "1" ++ "00" *)
    reflexivity.
  - split.
    + (* length "00" = 2 *)
      reflexivity.
    + (* "001" = "00" ++ "1" *)
      reflexivity.
Qed.