Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["999999999/1"; "1/1000000000"] -> x1=999999999, x2=1, n1=1, n2=1000000000
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 999999999 1 1 1000000000 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (999999999 * 1) mod (1 * 1000000000) *)
    (* 999999999 * 1 = 999999999 *)
    (* 1 * 1000000000 = 1000000000 *)
    (* 999999999 mod 1000000000 = 999999999 *)
    (* Hypothesis becomes 999999999 = 0, which is impossible *)
    compute in H_mod.
    discriminate H_mod.
Qed.