Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["38/241"; "3880/241"] -> x1=38, x2=241, n1=3880, n2=241
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 38 241 3880 241 false.
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
    (* Calculate (38 * 3880) mod (241 * 241) *)
    vm_compute in H_mod.
    (* H_mod simplifies to 31278 = 0, which is false *)
    discriminate.
Qed.