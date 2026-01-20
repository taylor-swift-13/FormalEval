Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["111/7"; "468/136"] -> x1=111, x2=7, n1=468, n2=136
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 111 7 468 136 false.
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
    (* Evaluate the arithmetic in the hypothesis *)
    vm_compute in H_mod.
    (* H_mod reduces to 540 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.