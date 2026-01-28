Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["176/17"; "176/717"] -> x1=176, x2=17, n1=176, n2=717
   Output: false -> result=false
*)
Example test_simplify_new : simplify_spec 176 17 176 717 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* H_res: false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate modulo: (176 * 176) mod (17 * 717) *)
    (* 30976 mod 12189 = 6598 *)
    (* H_mod implies 6598 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.