Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["921/7939"; "921/13"] -> x1=921, x2=7939, n1=921, n2=13
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 921 7939 921 13 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H_contra.
    discriminate H_contra.
  - (* Right to Left: mod = 0 -> false = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (921 * 921) mod (7939 * 13) *)
    (* We use vm_compute to evaluate the arithmetic values *)
    vm_compute in H_mod.
    (* H_mod evaluates to 22585 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.