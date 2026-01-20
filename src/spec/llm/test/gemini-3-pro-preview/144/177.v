Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["453/38"; "13/77"] -> x1=453, x2=38, n1=13, n2=77
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 453 38 13 77 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (453 * 13) mod (38 * 77) *)
    (* 453 * 13 = 5889 *)
    (* 38 * 77 = 2926 *)
    (* 5889 mod 2926 = 37 *)
    compute in H_mod.
    discriminate H_mod.
Qed.