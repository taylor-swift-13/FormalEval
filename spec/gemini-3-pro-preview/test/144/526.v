Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11711/7"; "453/38"] -> x1=11711, x2=7, n1=453, n2=38
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 11711 7 453 38 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Since result is false, H_res is false = true, which is impossible *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* We need to show that mod = 0 implies false = true (contradiction) *)
    (* (11711 * 453) mod (7 * 38) reduces to 245 *)
    vm_compute in H_mod.
    (* H_mod is now 245 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.