Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["453/38"; "3080/24"] -> x1=453, x2=38, n1=3080, n2=24
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 453 38 3080 24 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (453 * 3080) mod (38 * 24) *)
    (* 453 * 3080 = 1395240 *)
    (* 38 * 24 = 912 *)
    (* 1395240 mod 912 = 120 *)
    (* H_mod becomes 120 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.