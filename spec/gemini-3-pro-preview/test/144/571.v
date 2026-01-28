Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["8453/384"; "34553/384"] -> x1=8453, x2=384, n1=34553, n2=384
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 8453 384 34553 384 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate values: 
       8453 * 34553 = 292076409
       384 * 384 = 147456
       292076409 mod 147456 = 113529
       113529 = 0 is false
    *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.