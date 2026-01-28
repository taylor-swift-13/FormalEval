Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["467/736"; "467/736"] -> x1=467, x2=736, n1=467, n2=736
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 467 736 467 736 false.
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
    (* Evaluate the modulo: (467 * 467) mod (736 * 736) *)
    (* 218089 mod 541696 = 218089 *)
    (* H_mod becomes 218089 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.