Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["2225/20"; "2225/20"] -> x1=2225, x2=20, n1=2225, n2=20
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 2225 20 2225 20 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (2225 * 2225) mod (20 * 20) *)
    (* (2225 * 2225) = 4950625 *)
    (* (20 * 20) = 400 *)
    (* 4950625 mod 400 = 225 *)
    (* 225 = 0 is false *)
    compute in H_mod.
    discriminate.
Qed.