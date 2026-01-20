Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["711/7"; "11/9"] -> x1=711, x2=7, n1=11, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 711 7 11 9 false.
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
    (* Simplify algebraic expressions: (711 * 11) mod (7 * 9) *)
    (* 711 * 11 = 7821 *)
    (* 7 * 9 = 63 *)
    (* 7821 mod 63 = 9 *)
    (* H_mod implies 9 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.