Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["7/25"; "16311/9"] -> x1=7, x2=25, n1=16311, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 7 25 16311 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (7 * 16311) mod (25 * 9) *)
    (* 7 * 16311 = 114177 *)
    (* 25 * 9 = 225 *)
    (* 114177 mod 225 = 102 *)
    (* The hypothesis H_mod becomes 102 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.