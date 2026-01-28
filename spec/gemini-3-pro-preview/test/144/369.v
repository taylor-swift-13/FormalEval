Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["45553/384"; "9999/0100"] -> x1=45553, x2=384, n1=9999, n2=100
   Output: false -> result=false
*)
Example test_simplify_case : simplify_spec 45553 384 9999 100 false.
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
    (* Calculate (45553 * 9999) mod (384 * 100) *)
    (* (45553 * 9999) = 455484447 *)
    (* (384 * 100) = 38400 *)
    (* 455484447 mod 38400 = 22047 *)
    (* 22047 <> 0, so H_mod is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.