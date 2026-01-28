Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4853/3384"; "4853/3384"] -> x1=4853, x2=3384, n1=4853, n2=3384
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 4853 3384 4853 3384 false.
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
    (* Calculate (4853 * 4853) mod (3384 * 3384) *)
    vm_compute in H_mod.
    (* H_mod reduces to 648697 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.