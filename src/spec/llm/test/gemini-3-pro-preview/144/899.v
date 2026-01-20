Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["23/5"; "116853/58"] -> x1=23, x2=5, n1=116853, n2=58
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 23 5 116853 58 false.
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
    (* Compute the modulo value to show it is not 0 *)
    vm_compute in H_mod.
    (* H_mod reduces to 189 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.