Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["46474/736"; "4674/736"] -> x1=46474, x2=736, n1=4674, n2=736
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 46474 736 4674 736 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: false = true -> ... (contradiction) *)
    intros H_contra.
    discriminate H_contra.
  - (* Right to Left: mod = 0 -> false = true *)
    intros H_mod.
    (* Compute the modulo value to show it is not 0 *)
    vm_compute in H_mod.
    (* H_mod reduces to a non-zero value = 0, which is a contradiction *)
    discriminate H_mod.
Qed.