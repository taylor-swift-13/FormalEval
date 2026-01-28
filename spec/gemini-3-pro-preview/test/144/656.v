Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["9176/9"; "23/5"] -> x1=9176, x2=9, n1=23, n2=5
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 9176 9 23 5 false.
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
    (* Calculate (9176 * 23) mod (9 * 5) *)
    (* 9176 * 23 = 211048 *)
    (* 9 * 5 = 45 *)
    (* 211048 mod 45 = 43 *)
    vm_compute in H_mod.
    (* H_mod reduces to 43 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.