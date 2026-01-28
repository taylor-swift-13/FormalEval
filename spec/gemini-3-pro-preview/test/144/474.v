Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["161111/78"; "9999/010"] -> x1=161111, x2=78, n1=9999, n2=10
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 161111 78 9999 10 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (161111 * 9999) mod (78 * 10) *)
    (* This reduces to 69 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate.
Qed.