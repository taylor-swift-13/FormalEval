Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["23/5922291"; "8577/291"] -> x1=23, x2=5922291, n1=8577, n2=291
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 23 5922291 8577 291 false.
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
    (* Evaluate the modulo arithmetic *)
    vm_compute in H_mod.
    (* H_mod reduces to 197271 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.