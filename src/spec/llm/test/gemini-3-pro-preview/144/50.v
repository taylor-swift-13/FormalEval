Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["68/8"; "33/4"] -> x1=68, x2=8, n1=33, n2=4
   Output: false -> result=false
*)
Example test_simplify_case : simplify_spec 68 8 33 4 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (68 * 33) mod (8 * 4) *)
    (* 68 * 33 = 2244 *)
    (* 8 * 4 = 32 *)
    (* 2244 mod 32 = 4 *)
    (* 4 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.