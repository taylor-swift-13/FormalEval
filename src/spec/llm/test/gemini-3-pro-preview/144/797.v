Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["163111/9"; "163111/9"] -> x1=163111, x2=9, n1=163111, n2=9
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 163111 9 163111 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    (* Here result is false, so false = true is a contradiction *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    (* We need to show that mod = 0 implies false = true *)
    (* Since false = true is False, we must show mod = 0 is False (contradiction) *)
    intros H_mod.
    (* Calculate the actual modulo value *)
    vm_compute in H_mod.
    (* H_mod reduces to 16 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.