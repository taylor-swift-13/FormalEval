Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["857/291"; "453/3384"] -> x1=857, x2=291, n1=453, n2=3384
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 857 291 453 3384 false.
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
    (* Simplify algebraic expressions: (857 * 453) mod (291 * 3384) *)
    (* We compute the value to show it is not 0 *)
    vm_compute in H_mod.
    (* H_mod becomes 388221 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.