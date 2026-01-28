Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["84453/384"; "333/8"] -> x1=84453, x2=384, n1=333, n2=8
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 84453 384 333 8 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate values to show contradiction: (84453 * 333) mod (384 * 8) <> 0 *)
    compute in H_mod.
    discriminate H_mod.
Qed.