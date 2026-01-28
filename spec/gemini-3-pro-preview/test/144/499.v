Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["47677/77366"; "453/3384336"] -> x1=47677, x2=77366, n1=453, n2=3384336
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 47677 77366 453 3384336 false.
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
    (* We need to show mod = 0 is a contradiction to prove false = true *)
    (* Calculate the modulo value *)
    vm_compute in H_mod.
    (* The computation shows a non-zero value equals 0, which is false *)
    discriminate H_mod.
Qed.