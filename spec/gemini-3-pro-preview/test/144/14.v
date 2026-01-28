Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["6/8"; "3/4"] -> x1=6, x2=8, n1=3, n2=4
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 6 8 3 4 false.
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
    (* Simplify algebraic expressions: (6 * 3) mod (8 * 4) *)
    (* 6 * 3 = 18 *)
    (* 8 * 4 = 32 *)
    (* 18 mod 32 = 18 *)
    (* H_mod implies 18 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.