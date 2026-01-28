Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["8857/2991"; "857/2991"] -> x1=8857, x2=2991, n1=857, n2=2991
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 8857 2991 857 2991 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* H_res : false = true *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (8857 * 857) mod (2991 * 2991) *)
    (* 8857 * 857 = 7590449 *)
    (* 2991 * 2991 = 8946081 *)
    (* 7590449 mod 8946081 = 7590449 <> 0 *)
    vm_compute in H_mod.
    discriminate.
Qed.