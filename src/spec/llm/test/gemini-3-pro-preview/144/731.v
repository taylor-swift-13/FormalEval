Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["6116/17"; "6116/17"] -> x1=6116, x2=17, n1=6116, n2=17
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 6116 17 6116 17 false.
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
    (* Evaluate the modulo expression: (6116 * 6116) mod (17 * 17) *)
    (* This evaluates to 186, so H_mod becomes 186 = 0 *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.