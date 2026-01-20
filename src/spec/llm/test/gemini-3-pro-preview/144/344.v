Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11711/7"; "3/8"] -> x1=11711, x2=7, n1=3, n2=8
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 11711 7 3 8 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (11711 * 3) mod (7 * 8) *)
    (* 35133 mod 56 = 21 *)
    (* 21 = 0 -> False *)
    compute in H_mod.
    discriminate H_mod.
Qed.