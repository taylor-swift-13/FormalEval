Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4553/3"; "163/5"] -> x1=4553, x2=3, n1=163, n2=5
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 4553 3 163 5 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (4553 * 163) mod (3 * 5) *)
    vm_compute in H_mod.
    (* H_mod reduces to 14 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.