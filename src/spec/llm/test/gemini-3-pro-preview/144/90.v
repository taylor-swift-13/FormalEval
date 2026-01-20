Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["25/20"; "1199/1"] -> x1=25, x2=20, n1=1199, n2=1
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 25 20 1199 1 false.
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
    (* Calculate modulo: (25 * 1199) mod (20 * 1) *)
    (* 25 * 1199 = 29975 *)
    (* 20 * 1 = 20 *)
    (* 29975 mod 20 = 15 *)
    (* H_mod implies 15 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.