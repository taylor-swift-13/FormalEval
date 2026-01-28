Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["176/9"; "380/4241"] -> x1=176, x2=9, n1=380, n2=4241
   Output: false -> result=false
*)
Example test_simplify_new : simplify_spec 176 9 380 4241 false.
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
    (* Compute values: 
       176 * 380 = 66880
       9 * 4241 = 38169
       66880 mod 38169 = 28711 
    *)
    vm_compute in H_mod.
    (* H_mod is now 28711 = 0, which is a contradiction *)
    discriminate.
Qed.