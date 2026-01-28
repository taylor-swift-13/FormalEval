Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["921/7939"; "23/25"] -> x1=921, x2=7939, n1=23, n2=25
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 921 7939 23 25 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo operation: (921 * 23) mod (7939 * 25) *)
    (* 21183 mod 198475 = 21183 *)
    vm_compute in H_mod.
    (* H_mod becomes 21183 = 0, which is false *)
    discriminate.
Qed.