Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["161111/78"; "9999/0910"] -> x1=161111, x2=78, n1=9999, n2=910
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 161111 78 9999 910 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Since result is false, H_res is false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* We need to show that the mod is not 0, leading to a contradiction *)
    vm_compute in H_mod.
    (* H_mod evaluates to non_zero = 0 *)
    discriminate H_mod.
Qed.