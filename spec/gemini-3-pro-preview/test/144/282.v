Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4674/74436"; "46674/7436"] -> x1=4674, x2=74436, n1=46674, n2=7436
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 4674 74436 46674 7436 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo expression to show it is not 0 *)
    vm_compute in H_mod.
    (* H_mod becomes 218154276 = 0, a contradiction *)
    discriminate H_mod.
Qed.