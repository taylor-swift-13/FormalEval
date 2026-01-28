Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["9999/01"; "9999/010"] -> x1=9999, x2=1, n1=9999, n2=10
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 9999 1 9999 10 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* We need to show that the modulo is not 0, contradicting H_mod *)
    (* (9999 * 9999) mod (1 * 10) *)
    (* 9999 * 9999 = 99980001 *)
    (* 1 * 10 = 10 *)
    (* 99980001 mod 10 = 1 *)
    assert (H_calc : (9999 * 9999) mod (1 * 10) = 1) by reflexivity.
    rewrite H_calc in H_mod.
    discriminate H_mod.
Qed.