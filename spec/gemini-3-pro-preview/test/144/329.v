Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["453353/3"; "6467/736"] -> x1=453353, x2=3, n1=6467, n2=736
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 453353 3 6467 736 false.
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
    (* We need to show that mod = 0 implies false = true.
       Since false = true is False, we need to show mod = 0 is False (i.e., mod <> 0).
       Let's compute the modulo value. *)
    vm_compute in H_mod.
    (* H_mod reduces to 667 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.