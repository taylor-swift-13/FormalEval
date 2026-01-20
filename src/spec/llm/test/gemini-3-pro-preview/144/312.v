Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["453/3384"; "1653/58"] -> x1=453, x2=3384, n1=1653, n2=58
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 453 3384 1653 58 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo to show it is not 0 *)
    (* (453 * 1653) mod (3384 * 58) reduces to 159993 *)
    compute in H_mod.
    (* H_mod is now 159993 = 0, which is false *)
    discriminate.
Qed.