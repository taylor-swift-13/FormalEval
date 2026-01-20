Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["131683/584619"; "16311/9"] -> x1=131683, x2=584619, n1=16311, n2=9
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 131683 584619 16311 9 false.
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
    (* Calculate modulo: (131683 * 16311) mod (584619 * 9) *)
    vm_compute in H_mod.
    (* H_mod reduces to 1160445 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.