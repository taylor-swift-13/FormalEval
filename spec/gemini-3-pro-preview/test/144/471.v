Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["3080/204"; "453/384"] -> x1=3080, x2=204, n1=453, n2=384
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 3080 204 453 384 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res implies false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (3080 * 453) mod (204 * 384) *)
    (* (3080 * 453) = 1395240 *)
    (* (204 * 384) = 78336 *)
    (* 1395240 mod 78336 = 63528 *)
    (* H_mod reduces to 63528 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.