Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1613/58"; "57597/2757775"] -> x1=1613, x2=58, n1=57597, n2=2757775
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 1613 58 57597 2757775 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Compute the modulo value to show it is not 0 *)
    vm_compute in H_mod.
    (* H_mod becomes 92903961 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.