Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["9217/73"; "380/41"] -> x1=9217, x2=73, n1=380, n2=41
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 9217 73 380 41 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (9217 * 380) mod (73 * 41) *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.