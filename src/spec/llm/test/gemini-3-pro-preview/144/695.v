Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["921/7939"; "99/100"] -> x1=921, x2=7939, n1=99, n2=100
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 921 7939 99 100 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res implies false = true *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate values: (921 * 99) mod (7939 * 100) *)
    (* 91179 mod 793900 = 91179 *)
    (* 91179 <> 0, so assumption H_mod is false *)
    vm_compute in H_mod.
    discriminate.
Qed.