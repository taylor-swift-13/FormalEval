Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["46367/77636"; "176/17"] -> x1=46367, x2=77636, n1=176, n2=17
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 46367 77636 176 17 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so false = true is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate modulo: (46367 * 176) mod (77636 * 17) *)
    (* This evaluates to 241720 = 0, which is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.