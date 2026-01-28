Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4353/38"; "380/241"] -> x1=4353, x2=38, n1=380, n2=241
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 4353 38 380 241 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Compute the values to show contradiction *)
    (* (4353 * 380) mod (38 * 241) evaluates to 5700 *)
    compute in H_mod.
    (* H_mod becomes 5700 = 0 *)
    discriminate.
Qed.