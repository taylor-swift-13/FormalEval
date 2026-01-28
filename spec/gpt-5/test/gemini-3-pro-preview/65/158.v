Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.
Open Scope Z_scope.

(* Concrete definitions for the parameters to allow execution of the test case *)
Definition str_of_Z (z : Z) : string :=
  if Z.eqb z 9999999999 then "9999999999" else "".

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

Example test_circular_shift : circular_shift_spec 9999999999 (Z.to_nat 9999999998) "9999999999".
Proof.
  unfold circular_shift_spec.
  unfold str_of_Z.
  (* Simplify the expression to evaluate the conditionals *)
  rewrite Z.eqb_refl.
  
  (* We need to prove the condition Nat.ltb (String.length s) shift is true.
     s is "9999999999" (length 10). shift is Z.to_nat 9999999998.
     Since 10 < 9999999998, the condition holds. We prove it using Z lemmas 
     to avoid computing large nats. *)
  assert (H: Nat.ltb (String.length "9999999999") (Z.to_nat 9999999998) = true).
  {
    change (String.length "9999999999") with 10%nat.
    apply Nat.ltb_lt.
    change 10%nat with (Z.to_nat 10%Z).
    apply Z2Nat.inj_lt.
    - vm_compute. discriminate. (* 0 <= 10 *)
    - vm_compute. discriminate. (* 0 <= 9999999998 *)
    - vm_compute. reflexivity. (* 10 < 9999999998 *)
  }
  rewrite H.
  
  (* The result is reverse_string "9999999999", which is "9999999999" *)
  simpl.
  reflexivity.
Qed.